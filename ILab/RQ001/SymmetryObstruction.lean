import Mathlib

/-!
# RQ-001 Phase I — Symmetry Obstruction

A Lean 4 / Mathlib formalization of the Phase-I symmetry obstruction used in

"Frame-Relative Structure in the Search for an Intelligence Criterion".

Mathematical content:

Let a group `G` act transitively on a space `V`.  If a subset `R : Set V`
is invariant under the action, then membership in `R` is constant across `V`.
Hence `R` is either empty or the whole space.

This is the formal core of the "structure-free relevance" obstruction:
without symmetry-breaking structure, a transitive symmetry does not permit a
nontrivial invariant deterministic selection.

The result is intentionally intelligence-neutral.
-/

namespace ILab.RQ001

universe u v

section SymmetryObstruction

variable {G : Type u} {V : Type v}
variable [Group G] [MulAction G V]

/-- `R` is invariant under the action when acting by any group element
preserves and reflects membership. -/
def ActionInvariant (R : Set V) : Prop :=
  ∀ (g : G) (x : V), x ∈ R ↔ g • x ∈ R

/-- The action is transitive when every point can be moved to every other
point by some group element. -/
def ActionTransitive : Prop :=
  ∀ x y : V, ∃ g : G, g • x = y

/-- The empty set is invariant under every action. -/
theorem actionInvariant_empty :
    ActionInvariant (G := G) (V := V) (∅ : Set V) := by
  intro g x
  simp

/-- The whole space is invariant under every action. -/
theorem actionInvariant_univ :
    ActionInvariant (G := G) (V := V) (Set.univ : Set V) := by
  intro g x
  simp

/-- Under a transitive action, an invariant subset has the same membership
truth value at every pair of points. -/
theorem invariant_membership_iff
    (R : Set V)
    (htrans : ActionTransitive (G := G) (V := V))
    (hinv : ActionInvariant (G := G) (V := V) R)
    (x y : V) :
    x ∈ R ↔ y ∈ R := by
  rcases htrans x y with ⟨g, hg⟩
  constructor
  · intro hx
    have hgx : g • x ∈ R := (hinv g x).mp hx
    simpa [hg] using hgx
  · intro hy
    have hgx : g • x ∈ R := by
      simpa [hg] using hy
    exact (hinv g x).mpr hgx

/-- **Symmetry obstruction.**
For a transitive group action, every invariant subset is trivial:
it is either empty or the whole space. -/
theorem transitive_invariant_eq_empty_or_univ
    (R : Set V)
    (htrans : ActionTransitive (G := G) (V := V))
    (hinv : ActionInvariant (G := G) (V := V) R) :
    R = ∅ ∨ R = Set.univ := by
  by_cases hEmpty : R = ∅
  · exact Or.inl hEmpty
  · right
    obtain ⟨x, hx⟩ : R.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    apply Set.eq_univ_of_forall
    intro y
    exact (invariant_membership_iff R htrans hinv x y).mp hx

/-- A nonempty invariant subset under a transitive action must be the whole
space. -/
theorem transitive_invariant_nonempty_eq_univ
    (R : Set V)
    (htrans : ActionTransitive (G := G) (V := V))
    (hinv : ActionInvariant (G := G) (V := V) R)
    (hne : R.Nonempty) :
    R = Set.univ := by
  rcases transitive_invariant_eq_empty_or_univ R htrans hinv with h | h
  · simpa [h] using hne
  · exact h

/-- Equivalently: a transitive action admits no subset that is simultaneously
invariant, nonempty, and proper. -/
theorem no_nonempty_proper_invariant
    (R : Set V)
    (htrans : ActionTransitive (G := G) (V := V))
    (hinv : ActionInvariant (G := G) (V := V) R) :
    ¬ (R.Nonempty ∧ R ≠ Set.univ) := by
  intro h
  exact h.2 (transitive_invariant_nonempty_eq_univ R htrans hinv h.1)

end SymmetryObstruction

end ILab.RQ001
