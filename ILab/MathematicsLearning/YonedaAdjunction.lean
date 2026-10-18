import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Exact Mathlib reuse for non-exercise ordinary-category material

Each alias retains the complete inferred Mathlib signature and proof, rather
than weakening its hypotheses or pretending it is an original iLab result.
The compiler audit traverses the aliased proof's axiom dependencies.
-/
namespace ILab.MathematicsLearning
open CategoryTheory Opposite
universe u v u' v'

/-- 2.3: fully faithful precisely means bijective hom maps. -/
abbrev fullyFaithfulIffBijective := @Functor.FullyFaithful.nonempty_iff_map_bijective
abbrev fullyFaithfulHomEquiv := @Functor.FullyFaithful.homEquiv
/-- 2.6: the two tests use actual hom-map bijections. -/
abbrev isoIffPostcompositionBijective := @CategoryTheory.isIso_iff_yoneda_map_bijective
abbrev isoIffPrecompositionBijective := @CategoryTheory.isIso_iff_coyoneda_map_bijective

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 2.7: representable presheaves determine objects up to isomorphism. -/
theorem yoneda_object_iso_iff (X Y : C) :
    Nonempty (X ≅ Y) ↔ Nonempty (yoneda.obj X ≅ yoneda.obj Y) :=
  ⟨fun ⟨e⟩ => ⟨yoneda.mapIso e⟩,
    fun ⟨e⟩ => ⟨(Functor.FullyFaithful.ofFullyFaithful yoneda).preimageIso e⟩⟩

/-- 3.1: unit/counit and both triangles are fields of this exact structure. -/
abbrev AdjunctionData := @CategoryTheory.Adjunction
abbrev adjunctionLeftTriangle := @Adjunction.left_triangle_components
abbrev adjunctionRightTriangle := @Adjunction.right_triangle_components
/-- 3.4: exactly the source's quasi-inverse data, without a triangle assumption. -/
structure QuasiInverseData (F : C ⥤ D) where
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ F ⋙ inverse
  counitIso : inverse ⋙ F ≅ 𝟭 D

def equivalenceToQuasiInverse (e : C ≌ D) : QuasiInverseData e.functor :=
  ⟨e.inverse, e.unitIso, e.counitIso⟩

/-- 3.4 and the unnumbered 3.5 upgrade: Mathlib adjusts the unit. -/
def quasiInverseToEquivalence {F : C ⥤ D} (q : QuasiInverseData F) : C ≌ D :=
  CategoryTheory.Equivalence.mk F q.inverse q.unitIso q.counitIso

/-- 3.5: invertible unit and counit yield an equivalence, including its inverse. -/
noncomputable abbrev adjunctionToEquivalence := @Adjunction.toEquivalence
/-- 3.6: the exact witness-based Mathlib essential-surjectivity predicate. -/
abbrev EssentiallySurjective := @Functor.EssSurj

/-- 3.7: the fundamental criterion in the source's quasi-inverse sense. -/
theorem quasi_inverse_iff_fully_faithful_essSurj (F : C ⥤ D) :
    Nonempty (QuasiInverseData F) ↔ F.Full ∧ F.Faithful ∧ F.EssSurj := by
  constructor
  · rintro ⟨q⟩
    let e := quasiInverseToEquivalence q
    exact ⟨e.full_functor, e.faithful_functor, e.essSurj_functor⟩
  · rintro ⟨hfull, hfaithful, hess⟩
    let : F.Full := hfull
    let : F.Faithful := hfaithful
    let : F.EssSurj := hess
    let : F.IsEquivalence := {}
    exact ⟨equivalenceToQuasiInverse F.asEquivalence⟩

end ILab.MathematicsLearning
