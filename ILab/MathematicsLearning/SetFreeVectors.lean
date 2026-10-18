import ILab.MathematicsLearning.SmallVectorSpaces
import Mathlib.Algebra.Module.TransferInstance

/-! The direct sum indexed by a small set is represented by the actual
graphs of its finitely supported coefficient functions. Its carrier belongs
to the source universe by subset and function-set closure. -/
namespace ILab.MathematicsLearning.SetFreeVectors
universe u

private instance finsuppSmall (A K : ZFSet.{u}) [Field K] : Small.{u} (A →₀ K) :=
  small_of_injective (f := fun f : A →₀ K => (f : A → K)) DFunLike.coe_injective

noncomputable def encode (A K : ZFSet.{u}) [Field K] (f : A →₀ K) : ZFSet.{u} :=
  SetFunction.graph (f : A → K)

theorem encode_injective (A K : ZFSet.{u}) [Field K] : Function.Injective (encode A K) := by
  intro f g h
  apply DFunLike.coe_injective
  exact (SetFunction.graphEquiv A K).injective (Subtype.ext h)

noncomputable def carrier (A K : ZFSet.{u}) [Field K] : ZFSet.{u} := ZFSet.range (encode A K)

noncomputable def equiv (A K : ZFSet.{u}) [Field K] : (A →₀ K) ≃ carrier A K :=
  Equiv.ofBijective (fun f => ⟨encode A K f, ZFSet.mem_range_self f⟩)
    ⟨by
      intro f g h
      exact encode_injective A K (congrArg (fun x : carrier A K => x.val) h), by
      intro G
      obtain ⟨f, hf⟩ := ZFSet.mem_range.mp G.property
      exact ⟨f, Subtype.ext hf⟩⟩

theorem carrier_mem {U A K : ZFSet.{u}} [Field K] (hU : SetUniverse U)
    (hA : A ∈ U) (hK : K ∈ U) : carrier A K ∈ U := by
  apply hU.subsets _ (hU.functions_mem hA hK)
  intro G hG
  obtain ⟨f, rfl⟩ := ZFSet.mem_range.mp hG
  exact ZFSet.mem_funs.mpr (SetFunction.graph_isFunc (f : A → K))

noncomputable def vectorStructure (A K : ZFSet.{u}) [Field K] :
    SmallVectorSpaces.Structure K (carrier A K) :=
  letI := (equiv A K).symm.addCommGroup
  ⟨inferInstance, ((equiv A K).symm.addEquiv).module K⟩

/-- The transport is an actual linear equivalence, preserving every operation. -/
noncomputable def linearEquiv (A K : ZFSet.{u}) [Field K] :
    letI := (vectorStructure A K).group
    letI := (vectorStructure A K).module
    (A →₀ K) ≃ₗ[K] carrier A K :=
  letI := (equiv A K).symm.addCommGroup
  (((equiv A K).symm.addEquiv).linearEquiv K).symm

/-- The distinct basis vectors give an injection of the exact indexing set. -/
noncomputable def basisVector (A K : ZFSet.{u}) [Field K] (a : A) : carrier A K :=
  equiv A K (Finsupp.single a 1)

theorem basisVector_injective (A K : ZFSet.{u}) [Field K] :
    Function.Injective (basisVector A K) :=
  (equiv A K).injective.comp (Finsupp.single_left_injective one_ne_zero)

end ILab.MathematicsLearning.SetFreeVectors
