import ILab.LinearAlgebra.Dimensions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Holstein, Satz 5.1.1, printed p. 74. The target need not be finite-dimensional. -/
namespace ILab.LinearAlgebra
open Module Function
variable {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

noncomputable def mapByBasis (b : Basis ι K V) (w : ι → W) : V →ₗ[K] W :=
  b.constr K w

theorem mapByBasisValues (b : Basis ι K V) (w : ι → W) (i : ι) :
    mapByBasis b w (b i) = w i :=
  b.constr_basis K w i

theorem mapByBasisUnique (b : Basis ι K V) (w : ι → W) :
    ∃! f : V →ₗ[K] W, ∀ i, f (b i) = w i := by
  refine ⟨mapByBasis b w, mapByBasisValues b w, ?_⟩
  intro f hf
  apply b.ext
  intro i
  rw [hf, mapByBasisValues]

theorem mapByBasisImage (b : Basis ι K V) (w : ι → W) :
    LinearMap.range (mapByBasis b w) = Submodule.span K (Set.range w) :=
  b.constr_range K

theorem mapByBasisInjective (b : Basis ι K V) (w : ι → W)
    (hw : LinearIndependent K w) : Injective (mapByBasis b w) :=
  b.injective_constr_of_linearIndependent hw

theorem mapByBasisIndependent (b : Basis ι K V) (w : ι → W)
    (hf : Injective (mapByBasis b w)) : LinearIndependent K w := by
  have h := b.linearIndependent.map' (mapByBasis b w)
    ((injectiveIffKernelZero (mapByBasis b w)).mp hf)
  simpa only [Function.comp_def, mapByBasisValues] using h

theorem mapByBasisInjectiveIff (b : Basis ι K V) (w : ι → W) :
    Injective (mapByBasis b w) ↔ LinearIndependent K w :=
  ⟨mapByBasisIndependent b w, mapByBasisInjective b w⟩

/-- Part 2: prescribe images on an independent family and extend from its span. -/
theorem extendIndependentImages (v : ι → V) (hv : LinearIndependent K v) (w : ι → W) :
    ∃ f : V →ₗ[K] W, ∀ i, f (v i) = w i := by
  let B := Basis.span hv
  let F := mapByBasis B w
  obtain ⟨g, hg⟩ := F.exists_extend
  refine ⟨g, fun i => ?_⟩
  have hi := congrArg (fun l : Submodule.span K (Set.range v) →ₗ[K] W => l (B i)) hg
  calc
    g (v i) = g ((B i : Submodule.span K (Set.range v)) : V) := by
      simp only [B, Basis.coe_span_apply]
    _ = F (B i) := hi
    _ = w i := mapByBasisValues B w i

end ILab.LinearAlgebra
