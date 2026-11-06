import ILab.LinearAlgebra.LinearMapsFamilies
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Module.Basic

/-! Holstein §3.4, printed58–61/PDF60–63.
The quotient constructions below are over an arbitrary field and arbitrary modules,
without finite-dimensional assumptions. The last example uses all convergent real
sequences and genuine filter limits, not a finite window or numerical convergence test.
The existing quotientKernelEquivImage is reused for the first isomorphism theorem.
-/
namespace ILab.LinearAlgebra
open Function Filter
open scoped Topology
universe u v w
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- 3.4.1: the relation is exactly difference membership. -/
def quotientSubspaceSetoid (U : Submodule K V) : Setoid V := U.quotientRel

theorem quotientSubspaceRelation (U : Submodule K V) (x y : V) :
    (quotientSubspaceSetoid U).r x y ↔ x - y ∈ U := U.quotientRel_def

theorem differenceInSubspaceEquivalence (U : Submodule K V) :
    Equivalence (fun x y : V => x - y ∈ U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; simpa using U.zero_mem
  · intro x y h; simpa only [neg_sub] using U.neg_mem h
  · intro x y z hxy hyz
    simpa only [sub_add_sub_cancel] using U.add_mem hxy hyz

/-- The whole class, not a chosen representative. -/
theorem quotientClassAsTranslate (U : Submodule K V) (x y : V) :
    U.mkQ y = U.mkQ x ↔ ∃ a ∈ U, y = x + a := by
  change (Submodule.Quotient.mk y : V ⧸ U) = Submodule.Quotient.mk x ↔ _
  rw [Submodule.Quotient.eq]
  constructor
  · intro h; exact ⟨y-x,h,by abel⟩
  · rintro ⟨a,ha,rfl⟩; simpa using ha

/-- 3.4.2: actual Mathlib quotient module over the given field. -/
def quotientVectorSpace (U : Submodule K V) : Module K (V ⧸ U) := inferInstance

def canonicalQuotientProjection (U : Submodule K V) : V →ₗ[K] V ⧸ U := U.mkQ

theorem quotientClassesEqual (U : Submodule K V) (x y : V) :
    canonicalQuotientProjection U x = canonicalQuotientProjection U y ↔ x-y ∈ U :=
  Submodule.Quotient.eq U

theorem quotientAdditionIndependent (U : Submodule K V) (x x' y y' : V)
    (hx : x-x' ∈ U) (hy : y-y' ∈ U) :
    U.mkQ (x+y) = U.mkQ (x'+y') := by
  apply (quotientClassesEqual U _ _).mpr
  convert U.add_mem hx hy using 1 <;> abel

theorem quotientScalarIndependent (U : Submodule K V) (a : K) (x y : V)
    (h : x-y ∈ U) : U.mkQ (a • x) = U.mkQ (a • y) := by
  apply (quotientClassesEqual U _ _).mpr
  simpa only [smul_sub] using U.smul_mem a h

theorem quotientProjectionCombination (U : Submodule K V) (a b : K) (x y : V) :
    canonicalQuotientProjection U (a • x + b • y) =
      a • canonicalQuotientProjection U x + b • canonicalQuotientProjection U y := by
  simp only [map_add,map_smul]

theorem subspaceProjectionSurjective (U : Submodule K V) :
    Surjective (canonicalQuotientProjection U) := U.mkQ_surjective

theorem quotientProjectionKernel (U : Submodule K V) :
    LinearMap.ker (canonicalQuotientProjection U) = U := U.ker_mkQ

/-- 3.4.3: the actual induced linear map on the quotient. -/
def inducedQuotientMap (U : Submodule K V) (f : V →ₗ[K] W)
    (h : U ≤ LinearMap.ker f) : V ⧸ U →ₗ[K] W := U.liftQ f h

theorem inducedQuotientMapValue (U : Submodule K V) (f : V →ₗ[K] W)
    (h : U ≤ LinearMap.ker f) (x : V) :
    inducedQuotientMap U f h (U.mkQ x) = f x := rfl

theorem inducedQuotientFactorization (U : Submodule K V) (f : V →ₗ[K] W)
    (h : U ≤ LinearMap.ker f) :
    (inducedQuotientMap U f h).comp (canonicalQuotientProjection U) = f :=
  U.liftQ_mkQ f h

theorem inducedQuotientMapUnique (U : Submodule K V) (f : V →ₗ[K] W)
    (h : U ≤ LinearMap.ker f) (g : V ⧸ U →ₗ[K] W)
    (hg : g.comp (canonicalQuotientProjection U) = f) :
    g = inducedQuotientMap U f h := by
  apply LinearMap.ext
  intro q
  obtain ⟨x,rfl⟩ := subspaceProjectionSurjective U q
  exact congrArg (fun k : V →ₗ[K] W => k x) hg

theorem quotientUniversalProperty (U : Submodule K V) (f : V →ₗ[K] W) :
    (∃! g : V ⧸ U →ₗ[K] W, g.comp (canonicalQuotientProjection U) = f) ↔
      U ≤ LinearMap.ker f := by
  constructor
  · rintro ⟨g,hg,_⟩ x hx
    rw [LinearMap.mem_ker, ← hg]
    change g (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero U).mpr hx,map_zero]
  · intro h
    exact ⟨inducedQuotientMap U f h, inducedQuotientFactorization U f h,
      fun g hg => inducedQuotientMapUnique U f h g hg⟩

theorem quotientRecoverMap (U : Submodule K V) (g : V ⧸ U →ₗ[K] W) :
    ∃ h : U ≤ LinearMap.ker (g.comp U.mkQ),
      inducedQuotientMap U (g.comp U.mkQ) h = g := by
  have h : U ≤ LinearMap.ker (g.comp U.mkQ) := by
    intro x hx
    change g (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero U).mpr hx,map_zero]
  exact ⟨h,(inducedQuotientMapUnique U _ h g rfl).symm⟩

/-- 3.4.4: reuse the existing verified quotient-to-image equivalence. -/
noncomputable def firstIsomorphismQuotient (f : V →ₗ[K] W) :
    (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f := quotientKernelEquivImage f

theorem firstIsomorphismRepresentative (f : V →ₗ[K] W) (x : V) :
    (firstIsomorphismQuotient f ((LinearMap.ker f).mkQ x) : W) = f x := rfl

theorem firstIsomorphismFactorization (f : V →ₗ[K] W) :
    (LinearMap.range f).subtype.comp
      ((firstIsomorphismQuotient f).toLinearMap.comp (LinearMap.ker f).mkQ) = f := by
  ext x; exact firstIsomorphismRepresentative f x

theorem firstIsomorphismUnique (f : V →ₗ[K] W)
    (e : (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f)
    (he : (LinearMap.range f).subtype.comp
      (e.toLinearMap.comp (LinearMap.ker f).mkQ) = f) :
    e = firstIsomorphismQuotient f := by
  ext q
  obtain ⟨x,rfl⟩ := (LinearMap.ker f).mkQ_surjective q
  exact congrArg (fun k : V →ₗ[K] W => k x) he

theorem firstIsomorphismExistsUnique (f : V →ₗ[K] W) :
    ∃! e : (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f,
      (LinearMap.range f).subtype.comp
        (e.toLinearMap.comp (LinearMap.ker f).mkQ) = f :=
  ⟨firstIsomorphismQuotient f,firstIsomorphismFactorization f,
    fun e he => firstIsomorphismUnique f e he⟩

/-- 3.4.5: Fin3 coordinates, with index2 the last coordinate. -/
def thirdCoordinateProjection : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 2

theorem thirdCoordinateKernel (x : Fin 3 → ℝ) :
    x ∈ LinearMap.ker thirdCoordinateProjection ↔ x 2 = 0 := Iff.rfl

theorem thirdCoordinateSurjective : Surjective thirdCoordinateProjection := by
  intro x; exact ⟨fun _ => x,rfl⟩

noncomputable def thirdCoordinateQuotientEquivalence :
    ((Fin 3 → ℝ) ⧸ LinearMap.ker thirdCoordinateProjection) ≃ₗ[ℝ] ℝ :=
  thirdCoordinateProjection.quotKerEquivOfSurjective thirdCoordinateSurjective

theorem thirdCoordinateQuotientValue (x : Fin 3 → ℝ) :
    thirdCoordinateQuotientEquivalence ((LinearMap.ker thirdCoordinateProjection).mkQ x) =
      x 2 := rfl

theorem thirdCoordinateInverse (x : ℝ) :
    thirdCoordinateQuotientEquivalence.symm x =
      (LinearMap.ker thirdCoordinateProjection).mkQ ![0,0,x] := by
  apply thirdCoordinateQuotientEquivalence.injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- 3.4.6: quotient by the embedded first summand, not by a different ambient type. -/
def externalSecondProjection : (V × W) →ₗ[K] W := LinearMap.snd K V W

def embeddedFirstSummand : Submodule K (V × W) := LinearMap.ker externalSecondProjection

theorem embeddedFirstSummandMembership (x : V × W) :
    x ∈ (embeddedFirstSummand : Submodule K (V × W)) ↔ x.2 = 0 := Iff.rfl

noncomputable def quotientExternalFirstSummand :
    ((V × W) ⧸ (embeddedFirstSummand : Submodule K (V × W))) ≃ₗ[K] W :=
  (externalSecondProjection : (V × W) →ₗ[K] W).quotKerEquivOfSurjective
    (fun w => ⟨(0,w),rfl⟩)

theorem quotientExternalFirstSummandValue (x : V × W) :
    quotientExternalFirstSummand
      ((embeddedFirstSummand : Submodule K (V × W)).mkQ x) = x.2 := rfl

theorem quotientExternalFirstSummandInverse (x : W) :
    (quotientExternalFirstSummand (K:=K) (V:=V) (W:=W)).symm x =
      (embeddedFirstSummand : Submodule K (V × W)).mkQ (0,x) := by
  apply quotientExternalFirstSummand.injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- 3.4.7: all convergent sequences, with actual infinite-domain convergence. -/
def convergentRealSequenceSpace : Submodule ℝ (ℕ → ℝ) where
  carrier := {a | ∃ L, Tendsto a atTop (𝓝 L)}
  zero_mem' := ⟨0,tendsto_const_nhds⟩
  add_mem' := by
    rintro a b ⟨L,hL⟩ ⟨M,hM⟩
    exact ⟨L+M,hL.add hM⟩
  smul_mem' := by
    rintro c a ⟨L,hL⟩
    exact ⟨c • L,hL.const_smul c⟩

noncomputable def convergentRealSequenceLimit (a : convergentRealSequenceSpace) : ℝ :=
  Classical.choose a.property

theorem convergentRealSequenceLimitTendsto (a : convergentRealSequenceSpace) :
    Tendsto (a : ℕ → ℝ) atTop (𝓝 (convergentRealSequenceLimit a)) :=
  Classical.choose_spec a.property

theorem convergentRealSequenceLimitUnique (a : convergentRealSequenceSpace) (L : ℝ)
    (h : Tendsto (a : ℕ → ℝ) atTop (𝓝 L)) : convergentRealSequenceLimit a = L :=
  tendsto_nhds_unique (convergentRealSequenceLimitTendsto a) h

noncomputable def convergentRealSequenceLimitMap : convergentRealSequenceSpace →ₗ[ℝ] ℝ where
  toFun := convergentRealSequenceLimit
  map_add' := fun a b => convergentRealSequenceLimitUnique (a+b) _
    ((convergentRealSequenceLimitTendsto a).add (convergentRealSequenceLimitTendsto b))
  map_smul' := fun c a => convergentRealSequenceLimitUnique (c • a) _
    ((convergentRealSequenceLimitTendsto a).const_smul c)

noncomputable def nullRealSequenceSubspace : Submodule ℝ convergentRealSequenceSpace :=
  LinearMap.ker convergentRealSequenceLimitMap

theorem nullRealSequenceMembership (a : convergentRealSequenceSpace) :
    a ∈ nullRealSequenceSubspace ↔ Tendsto (a : ℕ → ℝ) atTop (𝓝 0) := by
  change convergentRealSequenceLimit a = 0 ↔ _
  constructor
  · intro h; rw [← h]; exact convergentRealSequenceLimitTendsto a
  · exact convergentRealSequenceLimitUnique a 0

theorem convergentRealSequenceLimitSurjective : Surjective convergentRealSequenceLimitMap := by
  intro L
  refine ⟨⟨fun _ => L,⟨L,tendsto_const_nhds⟩⟩,?_⟩
  exact convergentRealSequenceLimitUnique _ L tendsto_const_nhds

theorem convergentSequenceClassesEqual (a b : convergentRealSequenceSpace) :
    nullRealSequenceSubspace.mkQ a = nullRealSequenceSubspace.mkQ b ↔
      convergentRealSequenceLimit a = convergentRealSequenceLimit b := by
  change (Submodule.Quotient.mk a : convergentRealSequenceSpace ⧸ nullRealSequenceSubspace) =
    Submodule.Quotient.mk b ↔ _
  rw [Submodule.Quotient.eq]
  change convergentRealSequenceLimitMap (a-b) = 0 ↔ _
  rw [map_sub,sub_eq_zero]; rfl

noncomputable def convergentSequenceQuotientEquivalence :
    (convergentRealSequenceSpace ⧸ nullRealSequenceSubspace) ≃ₗ[ℝ] ℝ :=
  convergentRealSequenceLimitMap.quotKerEquivOfSurjective convergentRealSequenceLimitSurjective

theorem convergentSequenceQuotientValue (a : convergentRealSequenceSpace) :
    convergentSequenceQuotientEquivalence (nullRealSequenceSubspace.mkQ a) =
      convergentRealSequenceLimit a := rfl

end ILab.LinearAlgebra
