import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Order.Zorn

/-! Holstein chapter 6. General fields; no finite-dimensional assumption.
Basis sets are represented by subtypes with the inclusion as basis family.
Zorn and the classical choice used by Mathlib are existing foundations,
not new iLab axioms. Browser experiments are not verified programs. -/
namespace ILab.LinearAlgebra
open Set Submodule Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def admissibleIndependentSets (M E : Set V) : Set (Set V) :=
  {A | LinearIndepOn K id A ∧ M ⊆ A ∧ A ⊆ E}

omit [AddCommGroup V] in
theorem inclusionOrderLaws (A B C : Set V) :
    A ⊆ A ∧ ((A ⊆ B) → (B ⊆ C) → A ⊆ C) ∧ ((A ⊆ B) → (B ⊆ A) → A = B) :=
  ⟨Subset.rfl, Subset.trans, Subset.antisymm⟩

theorem chainPairComparable {α : Type*} [PartialOrder α] {c : Set α}
    (hc : IsChain (· ≤ ·) c) {a b : α} (ha : a ∈ c) (hb : b ∈ c) :
    a ≤ b ∨ b ≤ a := by
  by_cases h : a = b
  · subst b; exact Or.inl le_rfl
  · exact hc ha hb h

theorem emptyChainEveryUpperBound {α : Type*} [Preorder α] (a : α) :
    a ∈ upperBounds (∅ : Set α) := by simp

theorem greatestImpliesMaximal {α : Type*} [PartialOrder α] {a : α}
    (ha : ∀ b, b ≤ a) : IsMax a := fun _ _ => ha _

theorem zornMaximalElement {α : Type*} [PartialOrder α] [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) : ∃ a : α, IsMax a :=
  zorn_le h

theorem emptySetIndependent : LinearIndepOn K id (∅ : Set V) :=
  linearIndepOn_empty K id

theorem admissibleNonempty {M E : Set V} (hM : LinearIndepOn K id M) (hME : M ⊆ E) :
    (admissibleIndependentSets (K := K) M E).Nonempty :=
  ⟨M, hM, Subset.rfl, hME⟩

theorem independentChainUnion {c : Set (Set V)}
    (hc : IsChain (· ⊆ ·) c) (hi : ∀ A ∈ c, LinearIndepOn K id A) :
    LinearIndepOn K id (⋃₀ c) :=
  linearIndepOn_sUnion_of_directed hc.directedOn hi

theorem nonemptyChainUnionAdmissible {M E : Set V} {c : Set (Set V)}
    (hc : c ⊆ admissibleIndependentSets (K := K) M E)
    (chain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ⋃₀ c ∈ admissibleIndependentSets (K := K) M E := by
  refine ⟨independentChainUnion chain (fun A hA => (hc hA).1), ?_, ?_⟩
  · obtain ⟨A, hA⟩ := hne
    exact (hc hA).2.1.trans (subset_sUnion_of_mem hA)
  · exact sUnion_subset (fun A hA => (hc hA).2.2)

theorem everyAdmissibleChainBounded {M E : Set V}
    (hM : LinearIndepOn K id M) (hME : M ⊆ E)
    (c : Set (Set V)) (hc : c ⊆ admissibleIndependentSets (K := K) M E)
    (chain : IsChain (· ⊆ ·) c) :
    ∃ B ∈ admissibleIndependentSets (K := K) M E, ∀ A ∈ c, A ⊆ B := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨M, ⟨hM, Subset.rfl, hME⟩, by simp⟩
  · exact ⟨⋃₀ c, nonemptyChainUnionAdmissible hc chain hne,
      fun A hA => subset_sUnion_of_mem hA⟩

theorem maximalIndependentBetween {M E : Set V}
    (hM : LinearIndepOn K id M) (hME : M ⊆ E) :
    ∃ B, Maximal (· ∈ admissibleIndependentSets (K := K) M E) B :=
  zorn_subset _ (everyAdmissibleChainBounded hM hME)

theorem maximalBetweenSpansGenerators {M E B : Set V}
    (hB : Maximal (· ∈ admissibleIndependentSets (K := K) M E) B) :
    E ⊆ span K B := by
  intro e he
  by_contra hn
  have hi : LinearIndepOn K id (insert e B) := by
    exact hB.prop.1.insert (by simpa using hn)
  have hnew : insert e B ∈ admissibleIndependentSets (K := K) M E :=
    ⟨hi, hB.prop.2.1.trans (subset_insert e B), insert_subset he hB.prop.2.2⟩
  have heB : e ∈ B := hB.mem_of_prop_insert hnew
  exact hn (subset_span heB)

theorem basisSetBetween {M E : Set V} (hE : span K E = ⊤)
    (hME : M ⊆ E) (hM : LinearIndepOn K id M) :
    ∃ B : Set V, M ⊆ B ∧ B ⊆ E ∧ LinearIndepOn K id B ∧ span K B = ⊤ := by
  obtain ⟨B, hB⟩ := maximalIndependentBetween hM hME
  refine ⟨B, hB.prop.2.1, hB.prop.2.2, hB.prop.1, ?_⟩
  apply top_unique
  rw [← hE]
  exact span_le.mpr (maximalBetweenSpansGenerators hB)

theorem indexedBasisBetween {M E : Set V} (hE : span K E = ⊤)
    (hME : M ⊆ E) (hM : LinearIndepOn K id M) :
    ∃ (B : Set V) (b : Basis B K V), M ⊆ B ∧ B ⊆ E ∧
      (∀ x : B, b x = (x : V)) ∧ Set.range b = B := by
  obtain ⟨B, hMB, hBE, hi, hs⟩ := basisSetBetween hE hME hM
  let b : Basis B K V := Basis.mk hi.linearIndependent_restrict
    (by simpa using (ge_of_eq hs))
  have hb : ∀ x : B, b x = (x : V) := fun x => Basis.mk_apply _ _ _
  refine ⟨B, b, hMB, hBE, hb, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩; rw [hb]; exact y.property
  · intro hx; exact ⟨⟨x, hx⟩, hb _⟩

theorem arbitraryBasisExists :
    ∃ (B : Set V) (b : Basis B K V), ∀ x : B, b x = (x : V) := by
  obtain ⟨B, b, _, _, hb, _⟩ := indexedBasisBetween
    (K := K) (M := ∅) (E := Set.univ) (span_univ (R := K) (M := V)) (empty_subset _) emptySetIndependent
  exact ⟨B, b, hb⟩

theorem arbitraryBasisSelection {E : Set V} (hE : span K E = ⊤) :
    ∃ (B : Set V) (b : Basis B K V), B ⊆ E ∧ Set.range b = B := by
  obtain ⟨B, b, _, hBE, _, hr⟩ := indexedBasisBetween hE (empty_subset E) emptySetIndependent
  exact ⟨B, b, hBE, hr⟩

theorem arbitraryBasisExtension {M : Set V} (hM : LinearIndepOn K id M) :
    ∃ (B : Set V) (b : Basis B K V), M ⊆ B ∧ Set.range b = B := by
  obtain ⟨B, b, hMB, _, _, hr⟩ := indexedBasisBetween
    (span_univ (R := K) (M := V)) (subset_univ M) hM
  exact ⟨B, b, hMB, hr⟩

theorem polynomialMonomialBasis (n : ℕ) :
    Polynomial.basisMonomials K n = Polynomial.monomial n (1 : K) := rfl

theorem polynomialBasisIndependent : LinearIndependent K (Polynomial.basisMonomials K) :=
  (Polynomial.basisMonomials K).linearIndependent

theorem polynomialBasisSpans : span K (Set.range (Polynomial.basisMonomials K)) = ⊤ :=
  (Polynomial.basisMonomials K).span_eq

end ILab.LinearAlgebra
