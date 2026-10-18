import ILab.MathematicsLearning.SetCategories
import ILab.MathematicsLearning.YonedaAdjunction

/-!
# Adjunctions and equivalences on the manuscript's set-coded categories

The object and hom types here are the membership types of `SetCategory`,
whose operations agree definitionally with the source operations. Functors
and transformations are transported through the proved data equivalences.
All universe bounds therefore remain the source's literal membership bounds.

Theorem 3.7 is not assigned as an exercise (the manuscript says “Next time”).
Its proof reuses Mathlib internally. No separate proof of any assigned source
exercise is exported here, including the pointwise natural-isomorphism test.
-/
namespace ILab.MathematicsLearning.SetCategory
open CategoryTheory
universe u
variable {U : ZFSet.{u}} {C D : SetCategory U}

/-- Definition 3.1. Mathlib has exactly unit, counit, and the two component
triangle equations as fields, on the represented source categories. -/
abbrev SourceAdjunction (L : SourceFunctor C D) (R : SourceFunctor D C) :=
  L.toMathlib ⊣ R.toMathlib

theorem sourceAdjunction_left_triangle {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R) (X : Object C) :
    D.compose (L.map (a.unit.app X)) (a.counit.app (L.obj X)) =
      D.identity (L.obj X).member := a.left_triangle_components X

theorem sourceAdjunction_right_triangle {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R) (Y : Object D) :
    C.compose (a.unit.app (R.obj Y)) (R.map (a.counit.app Y)) =
      C.identity (R.obj Y).member := a.right_triangle_components Y

/-- Definition 3.4. Existence, with no triangle condition added: a reverse
functor and natural unit/counit whose components have two-sided inverses. -/
def IsEquivalence (F : SourceFunctor C D) : Prop :=
  ∃ G : SourceFunctor D C,
    ∃ η : 𝟭 (Object C) ⟶ F.toMathlib ⋙ G.toMathlib,
    ∃ ε : G.toMathlib ⋙ F.toMathlib ⟶ 𝟭 (Object D),
      (∀ X, IsIsomorphism (η.app X)) ∧ (∀ Y, IsIsomorphism (ε.app Y))

/-- Definition 3.6's witnesses coincide with the library predicate on the
same objects and morphisms; no essential-smallness surrogate is used. -/
theorem essentiallySurjective_agrees (F : SourceFunctor C D) :
    IsEssentiallySurjective F ↔ F.toMathlib.EssSurj := by
  rw [essentially_surjective_iff]
  constructor
  · intro h Y
    obtain ⟨X, f, hf⟩ := h Y
    obtain ⟨g, hfg, hgf⟩ := hf
    exact ⟨X, ⟨{ hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩⟩
  · intro h Y
    obtain ⟨X, ⟨e⟩⟩ := h Y
    exact ⟨X, e.hom, (isIsomorphism_iff_isIso e.hom).mpr inferInstance⟩

/-- The complete non-exercise Fundamental Theorem 3.7, with Definition 2.3's
actual bijection condition and Definition 3.6's actual source witnesses. -/
theorem fundamental_theorem (F : SourceFunctor C D) :
    IsEquivalence F ↔ IsEssentiallySurjective F ∧ IsFullyFaithful F := by
  classical
  constructor
  · rintro ⟨G, η, ε, hη, hε⟩
    let : ∀ X, IsIso (η.app X) := fun X =>
      (isIsomorphism_iff_isIso (η.app X)).mp (hη X)
    let : ∀ Y, IsIso (ε.app Y) := fun Y =>
      (isIsomorphism_iff_isIso (ε.app Y)).mp (hε Y)
    let : IsIso η := NatIso.isIso_of_isIso_app η
    let : IsIso ε := NatIso.isIso_of_isIso_app ε
    let q : QuasiInverseData F.toMathlib := ⟨G.toMathlib, asIso η, asIso ε⟩
    obtain ⟨hfull, hfaith, hess⟩ :=
      (quasi_inverse_iff_fully_faithful_essSurj F.toMathlib).mp ⟨q⟩
    let := hfull
    let := hfaith
    exact ⟨(essentiallySurjective_agrees F).mpr hess,
      (Functor.FullyFaithful.ofFullyFaithful F.toMathlib).map_bijective⟩
  · rintro ⟨hess, hbij⟩
    let : F.toMathlib.Full := ⟨fun {X Y} => (hbij X Y).surjective⟩
    let : F.toMathlib.Faithful := ⟨fun {X Y} => (hbij X Y).injective⟩
    let : F.toMathlib.EssSurj := (essentiallySurjective_agrees F).mp hess
    obtain ⟨q⟩ := (quasi_inverse_iff_fully_faithful_essSurj F.toMathlib).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
    refine ⟨SourceFunctor.fromMathlib q.inverse, q.unitIso.hom, q.counitIso.hom, ?_, ?_⟩
    · intro X
      exact ⟨(q.unitIso.app X).inv, (q.unitIso.app X).hom_inv_id,
        (q.unitIso.app X).inv_hom_id⟩
    · intro Y
      exact ⟨(q.counitIso.app Y).inv, (q.counitIso.app Y).hom_inv_id,
        (q.counitIso.app Y).inv_hom_id⟩

/-- Example 3.5, first bullet. The strict inverse equations imply the
source's weaker equivalence condition, on the same set-coded categories. -/
theorem strict_inverse_is_equivalence (F : SourceFunctor C D)
    (G : SourceFunctor D C)
    (hGF : F.toMathlib ⋙ G.toMathlib = 𝟭 (Object C))
    (hFG : G.toMathlib ⋙ F.toMathlib = 𝟭 (Object D)) : IsEquivalence F := by
  let η := eqToIso hGF.symm
  let ε := eqToIso hFG
  refine ⟨G, η.hom, ε.hom, ?_, ?_⟩
  · intro X
    exact ⟨(η.app X).inv, (η.app X).hom_inv_id, (η.app X).inv_hom_id⟩
  · intro Y
    exact ⟨(ε.app Y).inv, (ε.app Y).hom_inv_id, (ε.app Y).inv_hom_id⟩

/-- Example 3.5, second bullet, including both left and right functors. -/
theorem adjoint_equivalences {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R)
    (hη : ∀ X, IsIsomorphism (a.unit.app X))
    (hε : ∀ Y, IsIsomorphism (a.counit.app Y)) :
    IsEquivalence L ∧ IsEquivalence R := by
  classical
  let : ∀ X, IsIso (a.unit.app X) := fun X =>
    (isIsomorphism_iff_isIso _).mp (hη X)
  let : ∀ Y, IsIso (a.counit.app Y) := fun Y =>
    (isIsomorphism_iff_isIso _).mp (hε Y)
  let : IsIso a.unit := NatIso.isIso_of_isIso_app _
  let : IsIso a.counit := NatIso.isIso_of_isIso_app _
  let η := asIso a.unit
  let ε := asIso a.counit
  refine ⟨⟨R, a.unit, a.counit, hη, hε⟩, L, ε.inv, η.inv, ?_, ?_⟩
  · intro Y
    exact ⟨(ε.app Y).hom, (ε.app Y).inv_hom_id, (ε.app Y).hom_inv_id⟩
  · intro X
    exact ⟨(η.app X).hom, (η.app X).inv_hom_id, (η.app X).hom_inv_id⟩

/-- The unnumbered Fact in Example 3.5: an equivalence can be equipped with
an adjunction having invertible unit and counit. No triangle is assumed. -/
theorem equivalence_promotes_to_adjoint (F : SourceFunctor C D) (h : IsEquivalence F) :
    ∃ G : SourceFunctor D C, ∃ a : SourceAdjunction F G,
      (∀ X, IsIsomorphism (a.unit.app X)) ∧
      (∀ Y, IsIsomorphism (a.counit.app Y)) := by
  classical
  obtain ⟨hess, hbij⟩ := (fundamental_theorem F).mp h
  let : F.toMathlib.Full := ⟨fun {X Y} => (hbij X Y).surjective⟩
  let : F.toMathlib.Faithful := ⟨fun {X Y} => (hbij X Y).injective⟩
  let : F.toMathlib.EssSurj := (essentiallySurjective_agrees F).mp hess
  let : F.toMathlib.IsEquivalence := {}
  let e := F.toMathlib.asEquivalence
  refine ⟨SourceFunctor.fromMathlib e.inverse, e.toAdjunction, ?_, ?_⟩
  · intro X
    exact ⟨(e.unitIso.app X).inv, (e.unitIso.app X).hom_inv_id,
      (e.unitIso.app X).inv_hom_id⟩
  · intro Y
    exact ⟨(e.counitIso.app Y).inv, (e.counitIso.app Y).hom_inv_id,
      (e.counitIso.app Y).inv_hom_id⟩

end ILab.MathematicsLearning.SetCategory
