import ILab.MathematicsLearning.SetRepresentableIsomorphism

/-!
# Theorem 2.1: author-supplied construction data only

Moser–Walde, page 9, explicitly give evaluation at the identity and the
candidate inverse's component functions. The source assigns naturality of
that family, mutual inverseness, and naturality in c and F as exercises.
None of those checks is supplied here: the candidate has a function type,
not a natural-transformation type. The existing small-set representable is
reused as an input to evaluation, not proved again or counted as an exercise
solution. All carriers are the original ZFC set membership types.
-/
namespace ILab.MathematicsLearning.SetCategory
universe u
open CategoryTheory Opposite

variable (H : UniverseHierarchy.{u}) (C : SetCategory H.large)
    (hC : C.IsLocallySmall H.small)
    (F : (Object C)ᵒᵖ ⥤ Object (smallSetsCategory H)) (c : Object C)

/-- The authors' forward function: alpha maps to alpha_c(id_c).
The input is an already given natural transformation. No inverse is asserted. -/
noncomputable def yonedaEvaluation
    (α : representableInSmallSets H C hC c ⟶ F) :
    (F.obj (op c)).member.val :=
  (SetFunction.funsEquiv _ _).symm (α.app (op c)) (C.identity c.member)

/-- The authors' proposed inverse, only as its stated component functions:
for u in F(c), x in C and f : x -> c, return F(f)(u).
This does not package the family as a natural transformation. -/
noncomputable def yonedaCandidateComponent
    (u : (F.obj (op c)).member.val) (x : Object C) (f : x ⟶ c) :
    (F.obj (op x)).member.val :=
  (SetFunction.funsEquiv _ _).symm (F.map f.op) u

/-- Definitional readback of the supplied evaluation formula only. -/
theorem yonedaEvaluation_formula
    (α : representableInSmallSets H C hC c ⟶ F) :
    yonedaEvaluation H C hC F c α =
      (SetFunction.funsEquiv _ _).symm (α.app (op c)) (C.identity c.member) := rfl

/-- Definitional readback of the supplied component formula only. -/
theorem yonedaCandidateComponent_formula
    (u : (F.obj (op c)).member.val) (x : Object C) (f : x ⟶ c) :
    yonedaCandidateComponent H C F c u x f =
      (SetFunction.funsEquiv _ _).symm (F.map f.op) u := rfl

end ILab.MathematicsLearning.SetCategory
