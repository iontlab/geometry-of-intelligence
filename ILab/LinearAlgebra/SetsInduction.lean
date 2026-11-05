import ILab.LinearAlgebra.Logic
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Holstein 1.5, pp.20--25. Typed Set α identities, not a formalization of ZFC.
The contradictory Russell specification is refuted, never assumed to exist.
Prime factor existence is stated for n>1 (zero is excluded explicitly).
No uniqueness claim or formal verification of browser algorithms. -/
namespace ILab.LinearAlgebra

theorem setExtensionality {α : Type*} (A B : Set α)
    (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := Set.ext h

theorem setEqualityBySubsets {α : Type*} (A B : Set α) :
    A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h; subst B; exact ⟨fun _ h => h, fun _ h => h⟩
  · rintro ⟨h, k⟩; exact Set.Subset.antisymm h k

theorem singletonSubsetMembership {α : Type*} (x : α) (A : Set α) :
    ({x} : Set α) ⊆ A ↔ x ∈ A := Set.singleton_subset_iff

theorem emptySubsetEverySet {α : Type*} (A : Set α) : (∅ : Set α) ⊆ A :=
  Set.empty_subset A

theorem intersectionMembership {α : Type*} (x : α) (A B : Set α) :
    x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl

theorem unionMembership {α : Type*} (x : α) (A B : Set α) :
    x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl

theorem differenceMembership {α : Type*} (x : α) (A B : Set α) :
    x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := Iff.rfl

theorem powersetMembership {α : Type*} (A B : Set α) :
    B ∈ 𝒫 A ↔ B ⊆ A := Set.mem_powerset_iff B A

theorem indexedIntersectionMembership {α ι : Type*} (x : α) (A : ι → Set α) :
    x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i := Set.mem_iInter

theorem indexedUnionMembership {α ι : Type*} (x : α) (A : ι → Set α) :
    x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := Set.mem_iUnion

theorem emptyIndexedIntersection {α : Type*} (A : Empty → Set α) :
    (⋂ i, A i) = Set.univ := by
  ext x; simp

theorem emptyIndexedUnion {α : Type*} (A : Empty → Set α) :
    (⋃ i, A i) = ∅ := by
  ext x; simp

theorem setIntersectionCommutative {α : Type*} (A B : Set α) : A ∩ B = B ∩ A :=
  setExtensionality _ _ (fun x => conjunctionCommutative (x ∈ A) (x ∈ B))

theorem setUnionCommutative {α : Type*} (A B : Set α) : A ∪ B = B ∪ A :=
  setExtensionality _ _ (fun x => disjunctionCommutative (x ∈ A) (x ∈ B))

theorem setIntersectionAssociative {α : Type*} (A B C : Set α) :
    (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
  setExtensionality _ _ (fun x => conjunctionAssociative (x ∈ A) (x ∈ B) (x ∈ C))

theorem setUnionAssociative {α : Type*} (A B C : Set α) :
    A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
  setExtensionality _ _ (fun x => (disjunctionAssociative (x ∈ A) (x ∈ B) (x ∈ C)).symm)

theorem setIntersectionDistributes {α : Type*} (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  setExtensionality _ _ (fun x => conjunctionDistributes (x ∈ A) (x ∈ B) (x ∈ C))

theorem setUnionDistributes {α : Type*} (A B C : Set α) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  setExtensionality _ _ (fun x => disjunctionDistributes (x ∈ A) (x ∈ B) (x ∈ C))

theorem differenceNotCommutative :
    ({0} : Set ℕ) \ {1} ≠ ({1} : Set ℕ) \ {0} := by
  intro h
  have hz : 0 ∈ ({0} : Set ℕ) \ {1} := by simp
  rw [h] at hz
  simp at hz

/-- General relation formulation. No untyped universe is postulated. -/
theorem russellSpecificationImpossible {U : Type*} (mem : U → U → Prop) :
    ¬∃ r, ∀ x, mem x r ↔ ¬mem x x := by
  rintro ⟨r, h⟩
  have hr := h r
  have hn : ¬mem r r := fun hp => (hr.mp hp) hp
  exact hn (hr.mpr hn)

theorem finitePowersetCard {α : Type*} (A : Finset α) :
    A.powerset.card = 2 ^ A.card := Finset.card_powerset A

theorem naturalSuccessorNonzero (n : ℕ) : Nat.succ n ≠ 0 := Nat.succ_ne_zero n

theorem naturalSuccessorInjective {m n : ℕ} (h : Nat.succ m = Nat.succ n) : m = n :=
  Nat.succ.inj h

theorem inductionPrinciple (P : ℕ → Prop) (h0 : P 0)
    (hs : ∀ n, P n → P (n+1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

theorem inductiveSubsetEqualsNaturals (M : Set ℕ) (h0 : 0 ∈ M)
    (hs : ∀ n, n ∈ M → n+1 ∈ M) : M = Set.univ :=
  setExtensionality _ _ (fun n => ⟨fun _ => True.intro,
    fun _ => inductionPrinciple (fun k => k ∈ M) h0 hs n⟩)

theorem factorialInitialValue : Nat.factorial 0 = 1 := rfl

theorem factorialSuccessor (n : ℕ) : Nat.factorial (n+1) = (n+1)*Nat.factorial n :=
  Nat.factorial_succ n

theorem additionRecursion (m n : ℕ) : m + (n+1) = (m+n)+1 := rfl

theorem multiplicationRecursion (m n : ℕ) : m * (n+1) = m*n+m := Nat.mul_succ m n

theorem oddNumbersSum (n : ℕ) : (∑ i ∈ Finset.range n, (2*i+1)) = n^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem strongInductionPrinciple (P : ℕ → Prop)
    (hs : ∀ n, (∀ k, k < n → P k) → P n) : ∀ n, P n := by
  intro n
  exact Nat.strong_induction_on n hs

theorem smallestCounterexample (P : ℕ → Prop) (h : ∃ n, ¬P n) :
    ∃ m, ¬P m ∧ ∀ k, k < m → P k := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro k hk
  exact Classical.byContradiction (Nat.find_min h hk)

theorem descentExcludesCounterexamples (P : ℕ → Prop)
    (hs : ∀ n, ¬P n → ∃ k, k < n ∧ ¬P k) : ∀ n, P n := by
  classical
  by_contra h
  obtain ⟨m, hm, hmin⟩ := smallestCounterexample P (Classical.not_forall.mp h)
  obtain ⟨k, hk, hn⟩ := hs m hm
  exact hn (hmin k hk)

/-- Exact range correction: existence for n>1, not zero; uniqueness is not asserted. -/
theorem primeFactorizationExists (n : ℕ) (hn : 1 < n) :
    ∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ ps.prod = n := by
  refine ⟨n.primeFactorsList, ?_, Nat.prod_primeFactorsList (by omega)⟩
  exact fun _ hp => Nat.prime_of_mem_primeFactorsList hp

/-- The concatenation step used in Holstein's smallest-counterexample argument. -/
theorem concatenatePrimeFactorizations {a b : ℕ} {ps qs : List ℕ}
    (hp : ∀ p ∈ ps, Nat.Prime p) (hq : ∀ q ∈ qs, Nat.Prime q)
    (ha : ps.prod = a) (hb : qs.prod = b) :
    (∀ p ∈ ps ++ qs, Nat.Prime p) ∧ (ps ++ qs).prod = a*b := by
  constructor
  · intro p h; rcases List.mem_append.mp h with h | h
    · exact hp p h
    · exact hq p h
  · rw [List.prod_append, ha, hb]

/-- Holstein's actual minimal-counterexample argument, with explicit proper factors. -/
theorem primeFactorizationByMinimalCounterexample (n : ℕ) (hn : 1 < n) :
    ∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ ps.prod = n := by
  classical
  by_contra h
  let P := fun m : ℕ => 1 < m → ∃ ps : List ℕ,
    (∀ p ∈ ps, Nat.Prime p) ∧ ps.prod = m
  have hex : ∃ m, ¬P m := ⟨n, fun hp => h (hp hn)⟩
  obtain ⟨m, hm, hmin⟩ := smallestCounterexample P hex
  have hm1 : 1 < m := by
    by_contra hle
    exact hm (fun hlt => (hle hlt).elim)
  have hnp : ¬Nat.Prime m := by
    intro hp
    apply hm
    intro _
    exact ⟨[m], by simpa using hp, by simp⟩
  obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hnp
  have ha1 : 1 < a := by nlinarith
  have hb1 : 1 < b := by nlinarith
  obtain ⟨ps,hps,hpa⟩ := hmin a ha ha1
  obtain ⟨qs,hqs,hqb⟩ := hmin b hb hb1
  have hc := concatenatePrimeFactorizations hps hqs hpa hqb
  apply hm
  intro _
  exact ⟨ps++qs,hc.1,hab ▸ hc.2⟩

theorem primeFactorizationOne :
    (∀ p ∈ ([] : List ℕ), Nat.Prime p) ∧ ([] : List ℕ).prod = 1 := by simp

theorem noPrimeFactorizationZero :
    ¬∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ ps.prod = 0 := by
  rintro ⟨ps, hp, hz⟩
  have hpos : 0 < ps.prod := by
    apply List.prod_pos
    intro p h
    exact (hp p h).pos
  omega

end ILab.LinearAlgebra
