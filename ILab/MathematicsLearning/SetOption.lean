import ILab.MathematicsLearning.SetUniverseClosure
import Mathlib.Logic.Equiv.Option

/-! A disjointly adjoined point, coded within the source set universe.
The new point is the empty set and an old element is its singleton. Thus the
carrier lies in the power set of the old carrier, without transitivity. -/
namespace ILab.MathematicsLearning.SetOption
universe u

private instance (A : ZFSet.{u}) : Small.{u} (Option A) :=
  small_of_injective (Equiv.optionCongr (equivShrink A)).injective

def encode {A : ZFSet.{u}} : Option A → ZFSet.{u}
  | none => ∅
  | some a => {a.val}

theorem singleton_ne_empty (a : ZFSet.{u}) : ({a} : ZFSet.{u}) ≠ ∅ := by
  intro h
  have ha : a ∈ ({a} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [h] at ha
  exact ZFSet.notMem_empty a ha

theorem encode_injective (A : ZFSet.{u}) : Function.Injective (@encode A) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => exact False.elim (singleton_ne_empty y.val h.symm)
  | some x =>
    cases y with
    | none => exact False.elim (singleton_ne_empty x.val h)
    | some y => exact congrArg some (Subtype.ext (ZFSet.singleton_inj.mp h))

noncomputable def carrier (A : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (@encode A)

noncomputable def equiv (A : ZFSet.{u}) : Option A ≃ carrier A :=
  Equiv.ofBijective (fun x => ⟨encode x, ZFSet.mem_range_self x⟩)
    ⟨by
      intro x y h
      exact encode_injective A (congrArg (fun z : carrier A => z.val) h), by
      intro z
      obtain ⟨x, hx⟩ := ZFSet.mem_range.mp z.property
      exact ⟨x, Subtype.ext hx⟩⟩

theorem carrier_mem {U A : ZFSet.{u}} (hU : SetUniverse U) (hA : A ∈ U) :
    carrier A ∈ U := by
  apply hU.subsets _ (hU.powersets A hA)
  intro z hz
  obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hz
  apply ZFSet.mem_powerset.mpr
  cases x with
  | none => exact ZFSet.empty_subset _
  | some x =>
    intro a ha
    have he := ZFSet.mem_singleton.mp ha
    rw [he]
    exact x.property

noncomputable def point (A : ZFSet.{u}) : carrier A := equiv A none

noncomputable def inclusion (A : ZFSet.{u}) (a : A) : carrier A := equiv A (some a)

theorem inclusion_injective (A : ZFSet.{u}) : Function.Injective (inclusion A) := by
  intro a b h
  exact Option.some.inj ((equiv A).injective h)

theorem inclusion_ne_point (A : ZFSet.{u}) (a : A) : inclusion A a ≠ point A := by
  intro h
  cases (equiv A).injective h

theorem point_or_inclusion (A : ZFSet.{u}) (x : carrier A) :
    x = point A ∨ ∃ a, x = inclusion A a := by
  obtain ⟨o, rfl⟩ := (equiv A).surjective x
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

end ILab.MathematicsLearning.SetOption
