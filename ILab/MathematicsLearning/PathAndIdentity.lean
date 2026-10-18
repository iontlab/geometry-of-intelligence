import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Checked parts of the introduction

Path equalities below are endpoint-fixed homotopies, not literal equalities
of parametrised paths. The fundamental groupoid is a one-truncation, not a
formalization of the source's all-dimensional infinity-groupoid or univalence.
-/
namespace ILab.MathematicsLearning
noncomputable section

abbrev pathCompositionAssociativity := @Path.Homotopy.transAssoc
abbrev pathLeftIdentity := @Path.Homotopy.reflTrans
abbrev pathRightIdentity := @Path.Homotopy.transRefl
abbrev pathRightInverse := @Path.Homotopy.reflTransSymm
abbrev pathLeftInverse := @Path.Homotopy.reflSymmTrans
abbrev PathGroupoid := FundamentalGroupoid

/-- Isomorphic groups agree on existence of an element of order two. -/
theorem order_two_invariant {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (∃ x : G, orderOf x = 2) ↔ ∃ y : H, orderOf y = 2 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e x, (e.orderOf_eq x).trans hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨e.symm y, (e.symm.orderOf_eq y).trans hy⟩

/-- The source's two presentations: addition modulo two and multiplication of signs. -/
def cyclicTwoSigns : Multiplicative (ZMod 2) ≃* ℤˣ where
  toFun x := (-1 : ℤˣ) ^ (Multiplicative.toAdd x : ZMod 2)
  invFun s := Multiplicative.ofAdd (if s = 1 then 0 else 1)
  left_inv x := by
    have h (a : ZMod 2) : (if (-1 : ℤˣ) ^ a = 1 then (0 : ZMod 2) else 1) = a := by
      fin_cases a
      · change (if (1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 0
        simp
      · change (if (-1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 1
        norm_num
    exact congrArg Multiplicative.ofAdd (h (Multiplicative.toAdd x))
  right_inv s := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> norm_num
  map_mul' x y := by
    exact uzpow_add (-1 : ℤˣ) (Multiplicative.toAdd x) (Multiplicative.toAdd y)

theorem cyclic_two_zero_maps_to_one :
    cyclicTwoSigns (Multiplicative.ofAdd (0 : ZMod 2)) = 1 := by
  simp [cyclicTwoSigns]

theorem cyclic_two_one_maps_to_neg_one :
    cyclicTwoSigns (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
  simp [cyclicTwoSigns]

end
end ILab.MathematicsLearning
