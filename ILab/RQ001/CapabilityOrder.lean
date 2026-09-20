import Mathlib

/-!
# RQ-001 Phase I — Capability Order

A Lean 4 / Mathlib formalization of Proposition 1 and its immediate
monotonicity consequence from

"Frame-Relative Structure in the Search for an Intelligence Criterion".

The formalization is intentionally intelligence-neutral.  It assumes only:
* a type `R` of system realizations,
* a type `C` of challenges,
* an explicitly supplied success relation `Succeeds : R → C → Prop`.

Capability dominance is inclusion of realized capability sets.
-/

namespace ILab.RQ001

universe u v

section CapabilityOrder

variable {R : Type u} {C : Type v}

/-- The challenges on which realization `S` succeeds. -/
def Cap (Succeeds : R → C → Prop) (S : R) : Set C :=
  {c | Succeeds S c}

/-- Capability dominance: every challenge solved by `S` is also solved by `T`. -/
def CapLE (Succeeds : R → C → Prop) (S T : R) : Prop :=
  Cap Succeeds S ⊆ Cap Succeeds T

/-- Capability dominance is reflexive. -/
theorem capLE_refl (Succeeds : R → C → Prop) (S : R) :
    CapLE Succeeds S S := by
  intro c hc
  exact hc

/-- Capability dominance is transitive. -/
theorem capLE_trans (Succeeds : R → C → Prop) {S T U : R}
    (hST : CapLE Succeeds S T) (hTU : CapLE Succeeds T U) :
    CapLE Succeeds S U := by
  intro c hc
  exact hTU (hST hc)

/-- Mutual capability dominance is equality of capability sets. -/
def CapEq (Succeeds : R → C → Prop) (S T : R) : Prop :=
  Cap Succeeds S = Cap Succeeds T

/-- Equality of capability sets is exactly mutual dominance. -/
theorem capEq_iff_mutual (Succeeds : R → C → Prop) (S T : R) :
    CapEq Succeeds S T ↔
      (CapLE Succeeds S T ∧ CapLE Succeeds T S) := by
  constructor
  · intro h
    change Cap Succeeds S = Cap Succeeds T at h
    constructor
    · intro c hc
      rw [h] at hc
      exact hc
    · intro c hc
      rw [h]
      exact hc
  · rintro ⟨hST, hTS⟩
    exact Set.Subset.antisymm hST hTS

/-- The equivalence relation identifying realizations with equal capability sets. -/
def capSetoid (Succeeds : R → C → Prop) : Setoid R where
  r := CapEq Succeeds
  iseqv := {
    refl := by
      intro S
      rfl
    symm := by
      intro S T h
      exact h.symm
    trans := by
      intro S T U hST hTU
      exact hST.trans hTU
  }

/-- Realizations modulo equality of capability sets. -/
abbrev CapQuot (Succeeds : R → C → Prop) :=
  Quotient (capSetoid Succeeds)

/-- The capability set represented by a capability-equivalence class. -/
def quotCap (Succeeds : R → C → Prop) :
    CapQuot Succeeds → Set C :=
  Quotient.lift (Cap Succeeds) (by
    intro S T h
    exact h)

/-- Order on capability-equivalence classes induced by subset inclusion. -/
def QuotCapLE (Succeeds : R → C → Prop)
    (q₁ q₂ : CapQuot Succeeds) : Prop :=
  quotCap Succeeds q₁ ⊆ quotCap Succeeds q₂

/-- The quotient capability order is reflexive. -/
theorem quotCapLE_refl (Succeeds : R → C → Prop)
    (q : CapQuot Succeeds) :
    QuotCapLE Succeeds q q := by
  intro c hc
  exact hc

/-- The quotient capability order is transitive. -/
theorem quotCapLE_trans (Succeeds : R → C → Prop)
    {q₁ q₂ q₃ : CapQuot Succeeds}
    (h₁₂ : QuotCapLE Succeeds q₁ q₂)
    (h₂₃ : QuotCapLE Succeeds q₂ q₃) :
    QuotCapLE Succeeds q₁ q₃ := by
  intro c hc
  exact h₂₃ (h₁₂ hc)

/-- The quotient capability order is antisymmetric. -/
theorem quotCapLE_antisymm (Succeeds : R → C → Prop)
    {q₁ q₂ : CapQuot Succeeds}
    (h₁₂ : QuotCapLE Succeeds q₁ q₂)
    (h₂₁ : QuotCapLE Succeeds q₂ q₁) :
    q₁ = q₂ := by
  induction q₁ using Quotient.inductionOn with
  | _ S =>
      induction q₂ using Quotient.inductionOn with
      | _ T =>
          apply Quotient.sound
          change Cap Succeeds S = Cap Succeeds T
          apply Set.Subset.antisymm
          · exact h₁₂
          · exact h₂₁

/-- Hence capability classes carry a genuine partial order. -/
instance capQuotPartialOrder (Succeeds : R → C → Prop) :
    PartialOrder (CapQuot Succeeds) where
  le := QuotCapLE Succeeds
  le_refl := quotCapLE_refl Succeeds
  le_trans := by
    intro a b c hab hbc
    exact quotCapLE_trans Succeeds hab hbc
  le_antisymm := by
    intro a b hab hba
    exact quotCapLE_antisymm Succeeds hab hba

/-- The quotient embeds injectively into the set of capability profiles. -/
theorem quotCap_injective (Succeeds : R → C → Prop) :
    Function.Injective (quotCap Succeeds) := by
  intro q₁ q₂ h
  apply quotCapLE_antisymm Succeeds
  · intro c hc
    rw [h] at hc
    exact hc
  · intro c hc
    rw [h]
    exact hc

/-- The quotient realizes exactly the same family of capability sets as the
original realizations.  Combined with `quotCap_injective`, this identifies the
quotient with the family of realized capability profiles. -/
theorem quotCap_range (Succeeds : R → C → Prop) :
    Set.range (quotCap Succeeds) = Set.range (Cap Succeeds) := by
  ext A
  constructor
  · rintro ⟨q, rfl⟩
    exact Quotient.inductionOn q (fun S => ⟨S, rfl⟩)
  · rintro ⟨S, rfl⟩
    exact ⟨Quotient.mk _ S, rfl⟩

/-- A binary attribution is capability-monotone when dominance preserves it. -/
def CapabilityMonotone (Succeeds : R → C → Prop) (I : R → Prop) : Prop :=
  ∀ {S T : R}, CapLE Succeeds S T → I S → I T

/-- Capability extensionality: equal capability profiles receive equal
attributions. -/
def CapabilityExtensional (Succeeds : R → C → Prop) (I : R → Prop) : Prop :=
  ∀ {S T : R}, CapEq Succeeds S T → (I S ↔ I T)

/-- The corrected Phase-I consequence:
capability monotonicity implies capability extensionality. -/
theorem capabilityMonotone_implies_extensional
    (Succeeds : R → C → Prop) (I : R → Prop)
    (hmono : CapabilityMonotone Succeeds I) :
    CapabilityExtensional Succeeds I := by
  intro S T hEq
  have hmutual := (capEq_iff_mutual Succeeds S T).mp hEq
  constructor
  · intro hIS
    exact hmono hmutual.1 hIS
  · intro hIT
    exact hmono hmutual.2 hIT

end CapabilityOrder

end ILab.RQ001
