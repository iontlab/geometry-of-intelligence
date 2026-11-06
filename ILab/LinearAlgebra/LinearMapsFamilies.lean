import ILab.LinearAlgebra.VectorSpacesSubspaces
import ILab.LinearAlgebra.BasisMaps
import ILab.LinearAlgebra.RingsPolynomials
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Holstein §3.3, printed53–58. The sum equivalence targets U⊔W, not
the entire ambient space. The original inconsistent prime/minus notation is
documented separately. No categorical naturality theorem is claimed. -/
namespace ILab.LinearAlgebra
universe u v w z
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {T : Type z} [AddCommGroup T] [Module K T]

def preservesLinearCombinations (f : V → W) : Prop :=
  ∀ (a b : K) (v w : V), f (a • v + b • w) = a • f v + b • f w

def linearMapFromCombinedCondition (f : V → W) (h : preservesLinearCombinations (K:=K) f) :
    V →ₗ[K] W where
  toFun := f
  map_add' := by intro v w; simpa using h 1 1 v w
  map_smul' := by intro a v; simpa using h a 0 v 0

theorem linearityConditionsEquivalent (f : V → W) :
    preservesLinearCombinations (K:=K) f ↔
    (∀ v w, f (v+w)=f v+f w) ∧ (∀ (a:K) v, f (a • v)=a • f v) := by
  constructor
  · intro h
    exact ⟨(linearMapFromCombinedCondition f h).map_add,
      (linearMapFromCombinedCondition f h).map_smul⟩
  · rintro ⟨ha,hs⟩ a b v w
    rw [ha,hs,hs]

theorem linearMapCombination (f : V →ₗ[K] W) : preservesLinearCombinations (K:=K) f := by
  intro a b v w; simp
theorem linearMapFiniteCombination {ι : Type*} (f : V →ₗ[K] W)
    (s : Finset ι) (a : ι → K) (v : ι → V) :
    f (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i • f (v i) := by simp
theorem linearMapZeroDifference (f : V →ₗ[K] W) (v w : V) :
    f 0=0 ∧ f (v-w)=f v-f w := ⟨f.map_zero,f.map_sub v w⟩

def scalarLinearEndomorphism (a : K) : V →ₗ[K] V := a • LinearMap.id
theorem scalarEndomorphismValue (a : K) (v : V) : scalarLinearEndomorphism a v=a • v := rfl
theorem scalarEndomorphismBijective (a : K) (ha : a≠0) :
    Function.Bijective (scalarLinearEndomorphism (V:=V) a) := by
  constructor
  · intro v w h
    have := congrArg (fun x : V => a⁻¹ • x) h
    simpa [scalarLinearEndomorphism,ha] using this
  · intro v; exact ⟨a⁻¹ • v,by simp [scalarLinearEndomorphism,ha]⟩
theorem scalarFieldMapDetermined (f : K →ₗ[K] K) (x : K) : f x=f 1*x := by
  have h := f.map_smul x 1
  simpa [mul_comm] using h

def linearImageSubspace (f : V →ₗ[K] W) (U : Submodule K V) : Submodule K W := U.map f
def linearPreimageSubspace (f : V →ₗ[K] W) (U : Submodule K W) : Submodule K V := U.comap f
theorem linearImageMembership (f : V →ₗ[K] W) (U : Submodule K V) (w : W) :
    w∈linearImageSubspace f U ↔ ∃ v∈U,f v=w := Submodule.mem_map
theorem linearPreimageMembership (f : V →ₗ[K] W) (U : Submodule K W) (v : V) :
    v∈linearPreimageSubspace f U ↔ f v∈U := Iff.rfl
theorem linearKernelImage (f : V →ₗ[K] W) :
    (∀ v, v∈f.ker ↔ f v=0) ∧ (∀ w,w∈f.range ↔ ∃ v,f v=w) := by
  exact ⟨fun _=>Iff.rfl,fun _=>Iff.rfl⟩
def composeLinearMaps (g : W →ₗ[K] T) (f : V →ₗ[K] W) : V →ₗ[K] T := g.comp f
theorem compositionPreservesCombinations (g : W →ₗ[K] T) (f : V →ₗ[K] W) :
    preservesLinearCombinations (K:=K) (composeLinearMaps g f) := linearMapCombination _
noncomputable def inverseOfBijectiveLinearMap (f : V →ₗ[K] W) (h : Function.Bijective f) :
    W →ₗ[K] V := (LinearEquiv.ofBijective f h).symm.toLinearMap
theorem inverseLinearMapLaws (f : V →ₗ[K] W) (h : Function.Bijective f) (v : V) (w : W) :
    inverseOfBijectiveLinearMap f h (f v)=v ∧ f (inverseOfBijectiveLinearMap f h w)=w := by
  exact ⟨(LinearEquiv.ofBijective f h).symm_apply_apply v,
    (LinearEquiv.ofBijective f h).apply_symm_apply w⟩

theorem basisImagesDetermineLinearMap {ι : Type*} (b : Module.Basis ι K V) (f g : V →ₗ[K] W)
    (h : ∀ i,f (b i)=g (b i)) : f=g := b.ext h
theorem prescribedBasisImages {ι : Type*} (b : Module.Basis ι K V) (w : ι → W) :
    ∃! f : V →ₗ[K] W,∀ i,f (b i)=w i := mapByBasisUnique b w
theorem linearIsomorphismEquivalenceLaws :
    Nonempty (V ≃ₗ[K] V) ∧
    ((Nonempty (V ≃ₗ[K] W)) → Nonempty (W ≃ₗ[K] V)) ∧
    ((Nonempty (V ≃ₗ[K] W)) → (Nonempty (W ≃ₗ[K] T)) → Nonempty (V ≃ₗ[K] T)) := by
  exact ⟨⟨LinearEquiv.refl K V⟩,fun ⟨e⟩=>⟨e.symm⟩,fun ⟨e⟩ ⟨d⟩=>⟨e.trans d⟩⟩

def homSpaceAsFunctionSubmodule : Submodule K (V → W) where
  carrier := {f | preservesLinearCombinations (K:=K) f}
  zero_mem' := by intro a b v w; simp
  add_mem' := by
    intro f g hf hg a b v w
    change f (a • v+b • w)+g (a • v+b • w)=_
    rw [hf,hg]; simp only [Pi.add_apply,smul_add]; abel
  smul_mem' := by
    intro a f hf b c v w
    change a • f (b • v+c • w)=_
    rw [hf,smul_add]; simp only [Pi.smul_apply,smul_smul,mul_comm]
@[instance_reducible]
def linearHomSpaceModule : Module K (V →ₗ[K] W) := inferInstance
noncomputable def homSpaceFunctionEquivalence :
    (V →ₗ[K] W) ≃ₗ[K] homSpaceAsFunctionSubmodule (K:=K) (V:=V) (W:=W) where
  toFun := fun f=>⟨f,linearMapCombination f⟩
  invFun := fun f=>linearMapFromCombinedCondition f f.property
  left_inv := by intro f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; rfl
  map_smul' := by intro a f; rfl
theorem homSpacePointwiseOperations (f g : V →ₗ[K] W) (a : K) (v : V) :
    (f+g) v=f v+g v ∧ (a • f) v=a • f v := ⟨rfl,rfl⟩

def summationIntoSum (U Z : Submodule K V) : (U×Z) →ₗ[K] ↥(U⊔Z) :=
  (subspaceSummation U Z).codRestrict (U⊔Z) (by
    intro p
    exact Submodule.mem_sup.mpr ⟨p.1,p.1.property,p.2,p.2.property,rfl⟩)
theorem summationOntoSum (U Z : Submodule K V) : Function.Surjective (summationIntoSum U Z) := by
  intro v
  obtain ⟨x,hx,y,hy,hxy⟩:=Submodule.mem_sup.mp v.property
  exact ⟨(⟨x,hx⟩,⟨y,hy⟩),Subtype.ext hxy⟩
theorem summationIntoSumInjective (U Z : Submodule K V) (h : U⊓Z=⊥) :
    Function.Injective (summationIntoSum U Z) := by
  intro p q hpq
  apply (summationInjectiveIffTrivialIntersection U Z).mpr h
  exact congrArg Subtype.val hpq
noncomputable def externalPairInternalSumEquivalence (U Z : Submodule K V) (h : U⊓Z=⊥) :
    (U×Z) ≃ₗ[K] ↥(U⊔Z) :=
  LinearEquiv.ofBijective (summationIntoSum U Z)
    ⟨summationIntoSumInjective U Z h,summationOntoSum U Z⟩
theorem summationCompatibility (f : V →ₗ[K] W) (U Z : Submodule K V) (p : U×Z) :
    f (summationIntoSum U Z p)=f p.1+f p.2 := f.map_add _ _

def familyDirectSum {ι : Type*} (M : ι → Type*) [(i:ι)→AddCommGroup (M i)]
    [(i:ι)→Module K (M i)] := DirectSum ι M
theorem familyDirectSumFiniteSupport {ι : Type*} (M : ι → Type*)
    [(i:ι)→AddCommGroup (M i)] [(i:ι)→Module K (M i)] (v : DirectSum ι M) :
    Set.Finite {i | v i≠0} := by
  exact DFinsupp.finite_support v
noncomputable def polynomialCoefficientEquivalence : Polynomial K ≃ₗ[K] (ℕ →₀ K) :=
  (Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv _)
theorem polynomialCoefficientValue (p : Polynomial K) (n : ℕ) :
    polynomialCoefficientEquivalence p n=p.coeff n := rfl
noncomputable def polynomialDirectSumEquivalence :
    Polynomial K ≃ₗ[K] DirectSum ℕ (fun _=>K) :=
  polynomialCoefficientEquivalence.trans (finsuppLEquivDirectSum K K ℕ)
theorem polynomialDirectSumComponent (p : Polynomial K) (n : ℕ) :
    polynomialDirectSumEquivalence p n=p.coeff n := rfl
noncomputable def finiteCoordinateDirectSum (n : ℕ) :
    DirectSum (Fin n) (fun _=>K) ≃ₗ[K] (Fin n → K) := finiteExternalDirectSumEquivalence _
@[instance_reducible]
def familyProductModule {ι : Type*} (M : ι → Type*) [(i:ι)→AddCommGroup (M i)]
    [(i:ι)→Module K (M i)] : Module K ((i:ι)→M i) := inferInstance
theorem constantOneHasInfiniteSupport : ¬ Set.Finite {_n : ℕ | (1:K)≠0} := by
  simpa using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

end ILab.LinearAlgebra
