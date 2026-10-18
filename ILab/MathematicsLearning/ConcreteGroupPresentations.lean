import ILab.MathematicsLearning.PathAndIdentity
import Mathlib.Algebra.Group.TransferInstance

/-! Exact integer-carrier versions of the introduction's two group
presentations. These bridges justify the existing ZMod/units proof, including
the presentation-dependent assertion that the identity is the number zero. -/
namespace ILab.MathematicsLearning.ConcreteGroupPresentations

def ZeroOne := {z : ℤ // z = 0 ∨ z = 1}
def Signs := {z : ℤ // z = 1 ∨ z = -1}

noncomputable def zeroOneToCyclic : ZeroOne ≃ Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (x.val : ZMod 2)
  invFun x := ⟨(Multiplicative.toAdd x).val, by
    have h := (Multiplicative.toAdd x).val_lt
    omega⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨x, hx⟩
    rcases hx with rfl | rfl <;> decide
  right_inv x := by
    apply Multiplicative.toAdd.injective
    simp

noncomputable def signsToUnits : Signs ≃ ℤˣ where
  toFun x := ⟨x.val, x.val, by rcases x.property with h | h <;> simp [h],
    by rcases x.property with h | h <;> simp [h]⟩
  invFun x := ⟨x.val, by
    rcases Int.units_eq_one_or x with h | h
    · exact Or.inl (congrArg Units.val h)
    · exact Or.inr (congrArg Units.val h)⟩
  left_inv _ := rfl
  right_inv _ := Units.ext rfl

noncomputable instance zeroOneGroup : Group ZeroOne := zeroOneToCyclic.group
noncomputable instance signsGroup : Group Signs := signsToUnits.group

theorem zeroOne_multiplication (x y : ZeroOne) :
    (x * y).val = (x.val + y.val) % 2 := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem signs_multiplication (x y : Signs) : (x * y).val = x.val * y.val := rfl

theorem zeroOne_identity : (1 : ZeroOne).val = 0 := rfl
theorem signs_identity : (1 : Signs).val = 1 := rfl
theorem signs_identity_ne_zero : (1 : Signs).val ≠ 0 := by decide

noncomputable def presentationIso : ZeroOne ≃* Signs :=
  zeroOneToCyclic.mulEquiv.trans (cyclicTwoSigns.trans signsToUnits.mulEquiv.symm)

theorem order_two_property_agrees :
    (∃ x : ZeroOne, orderOf x = 2) ↔ ∃ y : Signs, orderOf y = 2 :=
  order_two_invariant presentationIso

end ILab.MathematicsLearning.ConcreteGroupPresentations
