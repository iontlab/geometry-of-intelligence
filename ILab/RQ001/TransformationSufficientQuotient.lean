import Mathlib

/-!
# RQ-001 Phase I — Transformation-Sufficient Quotient

Lean 4 / Mathlib formalization draft of the principal categorical construction
from:

"Frame-Relative Structure in the Search for an Intelligence Criterion"

Mathematical target (Phase-I Theorem M4.1):

* `E` is a category of declared environments / models.
* `X : E ⥤ Type uX` assigns a state space and transports states along declared
  transformations.
* Each object `d` carries an indexed family of retained probes.
* Two states at `e` are equivalent when every retained probe agrees after
  every admissible future transformation `e ⟶ d`.
* These equivalence relations are preserved by `X.map`.
* The quotients therefore assemble into a functor `Q`.
* The quotient maps form a natural transformation `q : X ⟶ Q`.
* Every local retained probe factors through `q.app e`.
* Universal property: for a second functor `Z : E ⥤ Type uX`, any
  pointwise-surjective natural abstraction `a : X ⟶ Z` through which all
  retained local probes factor admits a unique natural transformation
  `h : Z ⟶ Q` satisfying `a ≫ h = q`.

The shared codomain universe for `X` and `Z` is intentional: Mathlib natural
transformations are defined between functors with the same target category.
This is the direct Lean rendering of the paper's common-codomain statement
`X, Z : E → Set`.

This is a categorical construction about coherent abstraction.
It does NOT formalize a definition of intelligence.
-/

namespace ILab.RQ001

open CategoryTheory

universe uE vE uX uP uO

section TransformationSufficientQuotient

variable {E : Type uE} [Category.{vE, uE} E]

/- State/model assignment over the declared environment category. -/
variable (X : E ⥤ Type uX)

/- At each object, an index type for the retained probes/tests. -/
variable (Probe : E → Type uP)

/- Codomain of a retained probe may depend on both the object and probe. -/
variable (Obs : ∀ e : E, Probe e → Type uO)

/- Evaluation map for each retained probe. -/
variable (eval : ∀ (e : E) (p : Probe e), X.obj e → Obs e p)

/-- Transformation-sufficient equivalence at object `e`.

Two states are equivalent exactly when every retained probe agrees after every
declared transformation from `e` into any object `d`. -/
def TransformEq (e : E) (x x' : X.obj e) : Prop :=
  ∀ (d : E) (φ : e ⟶ d) (p : Probe d),
    eval d p (X.map φ x) = eval d p (X.map φ x')

/-- Transformation-sufficient equivalence is reflexive. -/
theorem transformEq_refl (e : E) (x : X.obj e) :
    TransformEq X Probe Obs eval e x x := by
  intro d φ p
  rfl

/-- Transformation-sufficient equivalence is symmetric. -/
theorem transformEq_symm (e : E) {x x' : X.obj e}
    (h : TransformEq X Probe Obs eval e x x') :
    TransformEq X Probe Obs eval e x' x := by
  intro d φ p
  exact (h d φ p).symm

/-- Transformation-sufficient equivalence is transitive. -/
theorem transformEq_trans (e : E) {x y z : X.obj e}
    (hxy : TransformEq X Probe Obs eval e x y)
    (hyz : TransformEq X Probe Obs eval e y z) :
    TransformEq X Probe Obs eval e x z := by
  intro d φ p
  exact (hxy d φ p).trans (hyz d φ p)

/-- The setoid induced by transformation-sufficient equivalence. -/
def transformSetoid (e : E) : Setoid (X.obj e) where
  r := TransformEq X Probe Obs eval e
  iseqv := {
    refl := transformEq_refl X Probe Obs eval e
    symm := by
      intro x y h
      exact transformEq_symm X Probe Obs eval e h
    trans := by
      intro x y z hxy hyz
      exact transformEq_trans X Probe Obs eval e hxy hyz
  }

/-- The transformation-sufficient quotient at object `e`. -/
abbrev TransformQuot (e : E) :=
  Quotient (transformSetoid X Probe Obs eval e)

/-- Equivalence is preserved by every declared transformation. -/
theorem transformEq_map {e d : E} (φ : e ⟶ d)
    {x x' : X.obj e}
    (h : TransformEq X Probe Obs eval e x x') :
    TransformEq X Probe Obs eval d (X.map φ x) (X.map φ x') := by
  intro k ψ p
  have hcomp := h k (φ ≫ ψ) p
  simpa using hcomp

/-- The quotient assignment is functorial. -/
def transformationQuotientFunctor : E ⥤ Type uX where
  obj e := TransformQuot X Probe Obs eval e
  map {e d} φ :=
    TypeCat.ofHom <| Quotient.lift (s := transformSetoid X Probe Obs eval e)
      (fun x : X.obj e =>
        (Quotient.mk _ (X.map φ x) : TransformQuot X Probe Obs eval d))
      (by
        intro x x' h
        apply Quotient.sound
        exact transformEq_map X Probe Obs eval φ h)
  map_id e := by
    ext q
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    have hx : X.map (𝟙 e) x = x := by
      simpa using congrFun (X.map_id e) x
    rw [hx]
  map_comp {e d k} φ ψ := by
    ext q
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    have hx :
        X.map (φ ≫ ψ) x = X.map ψ (X.map φ x) := by
      simpa using congrFun (X.map_comp φ ψ) x
    rw [hx]

/-- The canonical quotient maps assemble into a natural transformation. -/
def transformationQuotientNatTrans :
    X ⟶ transformationQuotientFunctor X Probe Obs eval where
  app e := TypeCat.ofHom (fun x => Quotient.mk _ x)
  naturality e d φ := by
    ext x
    rfl

/-- A retained local probe descends to the local quotient. -/
def probeDesc (e : E) (p : Probe e) :
    TransformQuot X Probe Obs eval e → Obs e p :=
  Quotient.lift (eval e p) (by
    intro x x' h
    change TransformEq X Probe Obs eval e x x' at h
    have hid := h e (𝟙 e) p
    simpa using hid)

/-- Local probes factor through the canonical quotient map. -/
theorem probe_factors_through_quotient
    (e : E) (p : Probe e) (x : X.obj e) :
    probeDesc X Probe Obs eval e p
        ((transformationQuotientNatTrans X Probe Obs eval).app e x)
      = eval e p x := by
  rfl

/-- Pointwise surjectivity of a natural abstraction. -/
def PointwiseSurjective {Z : E ⥤ Type uX} (a : X ⟶ Z) : Prop :=
  ∀ e : E, Function.Surjective (a.app e)

/-- Every retained local probe factors through the abstraction `a`. -/
def ProbesFactorThrough {Z : E ⥤ Type uX} (a : X ⟶ Z) : Prop :=
  ∀ (e : E) (p : Probe e),
    ∃ g : Z.obj e → Obs e p,
      eval e p = g ∘ a.app e

/-- If two states are identified by a natural abstraction preserving all local
retained probes, then they are transformation-sufficiently equivalent.

Naturality propagates equality under `a` through every future transformation;
local probe factorization then forces equality of every retained future test. -/
theorem nat_kernel_le_transformEq
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hfactors : ProbesFactorThrough X Probe Obs eval a)
    {e : E} {x x' : X.obj e}
    (hxx' : a.app e x = a.app e x') :
    TransformEq X Probe Obs eval e x x' := by
  intro d φ p
  rcases hfactors d p with ⟨g, hg⟩
  have hxnat :
      a.app d (X.map φ x) = Z.map φ (a.app e x) := by
    simpa using congrFun (a.naturality φ) x
  have hx'nat :
      a.app d (X.map φ x') = Z.map φ (a.app e x') := by
    simpa using congrFun (a.naturality φ) x'
  have ha :
      a.app d (X.map φ x) = a.app d (X.map φ x') := by
    calc
      a.app d (X.map φ x)
          = Z.map φ (a.app e x) := hxnat
      _ = Z.map φ (a.app e x') := by rw [hxx']
      _ = a.app d (X.map φ x') := hx'nat.symm
  calc
    eval d p (X.map φ x)
        = g (a.app d (X.map φ x)) := by
            rw [hg]
            rfl
    _ = g (a.app d (X.map φ x')) := congrArg g ha
    _ = eval d p (X.map φ x') := by
          rw [hg]
          rfl

noncomputable section

/-- A chosen right inverse to each pointwise-surjective component. -/
def chosenPreimage
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hsurj : PointwiseSurjective X a)
    (e : E) :
    Z.obj e → X.obj e :=
  fun z => Classical.choose (hsurj e z)

/-- The chosen preimage really maps to the requested point. -/
theorem chosenPreimage_spec
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hsurj : PointwiseSurjective X a)
    (e : E)
    (z : Z.obj e) :
    a.app e (chosenPreimage X a hsurj e z) = z := by
  exact Classical.choose_spec (hsurj e z)

/-- The universal factor from a pointwise-surjective, probe-preserving natural
abstraction into the transformation-sufficient quotient. -/
def quotientFactorNatTrans
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hsurj : PointwiseSurjective X a)
    (hfactors : ProbesFactorThrough X Probe Obs eval a) :
    Z ⟶ transformationQuotientFunctor X Probe Obs eval where
  app e := TypeCat.ofHom (fun z =>
    Quotient.mk _ (chosenPreimage X a hsurj e z))
  naturality e d φ := by
    ext z
    apply Quotient.sound
    apply nat_kernel_le_transformEq X Probe Obs eval a hfactors
    symm
    calc
      a.app d (X.map φ (chosenPreimage X a hsurj e z))
          = Z.map φ
              (a.app e (chosenPreimage X a hsurj e z)) := by
              simpa using congrFun (a.naturality φ)
                (chosenPreimage X a hsurj e z)
      _ = Z.map φ z := by
            rw [chosenPreimage_spec X a hsurj e z]
      _ = a.app d
            (chosenPreimage X a hsurj d (Z.map φ z)) := by
            symm
            exact chosenPreimage_spec X a hsurj d (Z.map φ z)

/-- The canonical quotient factors through every pointwise-surjective natural
abstraction that preserves the retained probes. -/
theorem quotientFactor_triangle
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hsurj : PointwiseSurjective X a)
    (hfactors : ProbesFactorThrough X Probe Obs eval a) :
    a ≫ quotientFactorNatTrans X Probe Obs eval a hsurj hfactors
      = transformationQuotientNatTrans X Probe Obs eval := by
  ext e x
  apply Quotient.sound
  apply nat_kernel_le_transformEq X Probe Obs eval a hfactors
  exact chosenPreimage_spec X a hsurj e (a.app e x)

/-- Uniqueness of the factor through the transformation-sufficient quotient. -/
theorem quotientFactor_unique
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hsurj : PointwiseSurjective X a)
    (hfactors : ProbesFactorThrough X Probe Obs eval a)
    (h : Z ⟶ transformationQuotientFunctor X Probe Obs eval)
    (htriangle :
      a ≫ h = transformationQuotientNatTrans X Probe Obs eval) :
    h = quotientFactorNatTrans X Probe Obs eval a hsurj hfactors := by
  ext e z
  rcases hsurj e z with ⟨x, rfl⟩
  have hh :
      h.app e (a.app e x)
        = (transformationQuotientNatTrans X Probe Obs eval).app e x := by
    simpa using
      ConcreteCategory.congr_hom (CategoryTheory.congr_app htriangle e) x
  have hq :
      (quotientFactorNatTrans X Probe Obs eval a hsurj hfactors).app e
          (a.app e x)
        = (transformationQuotientNatTrans X Probe Obs eval).app e x := by
    have htri :=
      quotientFactor_triangle X Probe Obs eval a hsurj hfactors
    simpa using
      ConcreteCategory.congr_hom (CategoryTheory.congr_app htri e) x
  exact hh.trans hq.symm

/-- **Transformation-sufficient quotient theorem.**

The quotient maps define a natural quotient preserving every retained local
probe. Among pointwise-surjective natural abstractions through which all local
retained probes factor, this quotient is coarsest: there exists a unique
natural transformation `h : Z ⟶ Q` with `a ≫ h = q`. -/
theorem transformation_sufficient_quotient_universal
    {Z : E ⥤ Type uX}
    (a : X ⟶ Z)
    (hsurj : PointwiseSurjective X a)
    (hfactors : ProbesFactorThrough X Probe Obs eval a) :
    ∃! h : Z ⟶ transformationQuotientFunctor X Probe Obs eval,
      a ≫ h = transformationQuotientNatTrans X Probe Obs eval := by
  refine ⟨quotientFactorNatTrans X Probe Obs eval a hsurj hfactors, ?_, ?_⟩
  · exact quotientFactor_triangle X Probe Obs eval a hsurj hfactors
  · intro h hh
    exact quotientFactor_unique X Probe Obs eval a hsurj hfactors h hh

end

end TransformationSufficientQuotient

end ILab.RQ001
