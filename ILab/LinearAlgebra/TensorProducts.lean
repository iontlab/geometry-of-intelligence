import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Holstein §12.9. The original source's characteristic-two and permutation
issues are retained in the native text, never assumed here. Exterior powers
below use Mathlib's alternating construction, not the sign-eigenspace in char 2.
All general statements are independent of the finite browser coordinate models. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace ILab.LinearAlgebra
open Module TensorProduct
open scoped TensorProduct BigOperators
universe u uι uκ
variable {K V W X Y Z : Type u} [Field K]
 [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
 [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
 [AddCommGroup Z] [Module K Z]

def tensorBilinear : V →ₗ[K] W →ₗ[K] V ⊗[K] W := TensorProduct.mk K V W

theorem tensorFirstLinear (a b : K) (v v' : V) (w : W) :
 (a • v + b • v') ⊗ₜ[K] w = a • (v ⊗ₜ[K] w) + b • (v' ⊗ₜ[K] w) := by
 simp [add_tmul, smul_tmul']

theorem tensorSecondLinear (a b : K) (v : V) (w w' : W) :
 v ⊗ₜ[K] (a • w + b • w') = a • (v ⊗ₜ[K] w) + b • (v ⊗ₜ[K] w') := by
 simp [tmul_add, tmul_smul]

theorem tensorZeroLeft (w : W) : (0 : V) ⊗ₜ[K] w = 0 := by simp
theorem tensorZeroRight (v : V) : v ⊗ₜ[K] (0 : W) = 0 := by simp

def tensorFactor (α : V →ₗ[K] W →ₗ[K] X) : V ⊗[K] W →ₗ[K] X := TensorProduct.lift α

theorem tensorFactorOnPure (α : V →ₗ[K] W →ₗ[K] X) (v : V) (w : W) :
 tensorFactor α (v ⊗ₜ[K] w) = α v w := TensorProduct.lift.tmul v w

theorem tensorUniversal (α : V →ₗ[K] W →ₗ[K] X) :
 ∃! F : V ⊗[K] W →ₗ[K] X, ∀ v w, F (v ⊗ₜ[K] w) = α v w := by
 refine ⟨tensorFactor α, tensorFactorOnPure α, ?_⟩
 intro F h
 exact TensorProduct.lift.unique h

theorem tensorMapExt (f g : V ⊗[K] W →ₗ[K] X)
 (h : ∀ v w, f (v ⊗ₜ[K] w) = g (v ⊗ₜ[K] w)) : f = g := TensorProduct.ext' h

def UniversalBilinear (κ : V →ₗ[K] W →ₗ[K] X) : Prop :=
 ∀ (T : Type u) [AddCommGroup T] [Module K T] (α : V →ₗ[K] W →ₗ[K] T),
 ∃! F : X →ₗ[K] T, ∀ v w, F (κ v w) = α v w

theorem canonicalTensorUniversal : UniversalBilinear (tensorBilinear (K:=K) (V:=V) (W:=W)) := by
 intro T _ _ α
 exact tensorUniversal α

theorem universalBilinearExt (κ : V →ₗ[K] W →ₗ[K] X) (hκ : UniversalBilinear κ)
 (f g : X →ₗ[K] Y) (h : ∀ v w, f (κ v w) = g (κ v w)) : f = g := by
 obtain ⟨F, hF, huniq⟩ := hκ Y (κ.compr₂ g)
 have hg : g = F := huniq g (by intro v w; rfl)
 have hf : f = F := huniq f (by intro v w; exact h v w)
 exact hf.trans hg.symm

theorem tensorUniqueComparison (κ : V →ₗ[K] W →ₗ[K] X) (κ' : V →ₗ[K] W →ₗ[K] Y)
 (hκ : UniversalBilinear κ) (hκ' : UniversalBilinear κ') :
 ∃! e : X ≃ₗ[K] Y, ∀ v w, e (κ v w) = κ' v w := by
 obtain ⟨f, hf, _⟩ := hκ Y κ'
 obtain ⟨g, hg, _⟩ := hκ' X κ
 have gf : g.comp f = LinearMap.id := universalBilinearExt κ hκ _ _ (by
   intro v w; simp only [LinearMap.comp_apply, LinearMap.id_apply, hf, hg])
 have fg : f.comp g = LinearMap.id := universalBilinearExt κ' hκ' _ _ (by
   intro v w; simp only [LinearMap.comp_apply, LinearMap.id_apply, hf, hg])
 let e : X ≃ₗ[K] Y := { f with invFun := g
                               left_inv := fun x => LinearMap.congr_fun gf x
                               right_inv := fun y => LinearMap.congr_fun fg y }
 refine ⟨e, hf, ?_⟩
 intro e' he'
 have he : e'.toLinearMap = f := universalBilinearExt κ hκ _ _ (by intro v w; exact (he' v w).trans (hf v w).symm)
 exact LinearEquiv.toLinearMap_injective he

def tensorBasis {ι : Type uι} {κ : Type uκ} (b : Basis ι K V) (c : Basis κ K W) :
 Basis (ι × κ) K (V ⊗[K] W) := b.tensorProduct c

def tensorFiniteSupport {ι : Type uι} {κ : Type uκ} (b : Basis ι K V) (c : Basis κ K W) :
 (V ⊗[K] W) ≃ₗ[K] ((ι × κ) →₀ K) := (tensorBasis b c).repr

theorem tensorBasisCoordinates {ι : Type uι} {κ : Type uκ} (b : Basis ι K V) (c : Basis κ K W)
 (v : V) (w : W) (i : ι) (j : κ) :
 tensorFiniteSupport b c (v ⊗ₜ[K] w) (i,j) = b.repr v i * c.repr w j := by
 simpa [tensorFiniteSupport, tensorBasis, mul_comm] using b.tensorProduct_repr_tmul_apply c v w i j

theorem tensorDimension [FiniteDimensional K V] [FiniteDimensional K W] :
 finrank K (V ⊗[K] W) = finrank K V * finrank K W := Module.finrank_tensorProduct

theorem tensorFinitePureSum (t : V ⊗[K] W) :
 ∃ l : List (V × W), (l.map (fun z => z.1 ⊗ₜ[K] z.2)).sum = t := by
 induction t using TensorProduct.induction_on with
 | zero => exact ⟨[], rfl⟩
 | tmul v w => exact ⟨[(v,w)], by simp⟩
 | add t s ht hs =>
   obtain ⟨l, hl⟩ := ht
   obtain ⟨m, hm⟩ := hs
   exact ⟨l++m, by simp [hl,hm]⟩

def tensorStandardCoordinates (m n : ℕ) :
 ((Fin m → K) ⊗[K] (Fin n → K)) ≃ₗ[K] (Fin m × Fin n → K) :=
 (tensorFiniteSupport (Pi.basisFun K (Fin m)) (Pi.basisFun K (Fin n))).trans
 (Finsupp.linearEquivFunOnFinite K K (Fin m × Fin n))

def tensorHomEquiv : (V ⊗[K] W →ₗ[K] X) ≃ₗ[K] (V →ₗ[K] W →ₗ[K] X) :=
 (TensorProduct.lift.equiv (RingHom.id K) V W X).symm

theorem tensorHomEvaluation (f : V ⊗[K] W →ₗ[K] X) (v : V) (w : W) :
 tensorHomEquiv f v w = f (v ⊗ₜ[K] w) := rfl

def tensorDualBilinear : Module.Dual K (V ⊗[K] W) ≃ₗ[K] (V →ₗ[K] W →ₗ[K] K) := tensorHomEquiv

def dualTensorLinearHom [FiniteDimensional K V] :
 Module.Dual K V ⊗[K] W ≃ₗ[K] (V →ₗ[K] W) := dualTensorHomEquiv K V W

theorem dualTensorRankOne [FiniteDimensional K V] (α : Module.Dual K V) (w : W) (v : V) :
 dualTensorLinearHom (α ⊗ₜ[K] w) v = α v • w := by
 exact dualTensorHom_apply α v w

/-- Two distinct variables are indexed by the two summands of PUnit ⊕ PUnit. -/
def polynomialTensorEquiv :
 (Polynomial K ⊗[K] Polynomial K) ≃ₗ[K] MvPolynomial (PUnit ⊕ PUnit) K :=
 (TensorProduct.congr (MvPolynomial.uniqueAlgEquiv K PUnit).symm.toLinearEquiv
   (MvPolynomial.uniqueAlgEquiv K PUnit).symm.toLinearEquiv).trans
   (MvPolynomial.tensorEquivSum K PUnit PUnit K).toLinearEquiv

theorem polynomialTensorDistinctVariables :
 polynomialTensorEquiv (Polynomial.X ⊗ₜ[K] (1 : Polynomial K)) = MvPolynomial.X (Sum.inl PUnit.unit) ∧
 polynomialTensorEquiv ((1 : Polynomial K) ⊗ₜ[K] Polynomial.X) = MvPolynomial.X (Sum.inr PUnit.unit) := by
 simp [polynomialTensorEquiv]

abbrev complexifiedModule (W : Type u) [AddCommGroup W] [Module ℝ W] := ℂ ⊗[ℝ] W

theorem complexifiedModuleStructure (W : Type u) [AddCommGroup W] [Module ℝ W] :
 Nonempty (Module ℂ (complexifiedModule W)) := ⟨inferInstance⟩

def complexifiedBasis {W : Type u} [AddCommGroup W] [Module ℝ W] {ι : Type u}
 (b : Basis ι ℝ W) : Basis ι ℂ (complexifiedModule W) := b.baseChange ℂ

theorem complexifiedBasisPure {W : Type u} [AddCommGroup W] [Module ℝ W] {ι : Type u}
 (b : Basis ι ℝ W) (i : ι) : complexifiedBasis b i = (1 : ℂ) ⊗ₜ[ℝ] b i := by
 simp [complexifiedBasis, Basis.baseChange_apply]

def inducedTensorMap (f : V →ₗ[K] X) (g : W →ₗ[K] Y) :
 V ⊗[K] W →ₗ[K] X ⊗[K] Y := TensorProduct.map f g

theorem inducedTensorOnPure (f : V →ₗ[K] X) (g : W →ₗ[K] Y) (v : V) (w : W) :
 inducedTensorMap f g (v ⊗ₜ[K] w) = f v ⊗ₜ[K] g w := TensorProduct.map_tmul _ _ _ _

theorem inducedTensorIdentity : inducedTensorMap (LinearMap.id : V →ₗ[K] V) (LinearMap.id : W →ₗ[K] W) = LinearMap.id := by
 ext v w; simp [inducedTensorMap]

theorem inducedTensorComposition (f : V →ₗ[K] X) (g : W →ₗ[K] Y)
 (a : X →ₗ[K] Z) (b : Y →ₗ[K] V) :
 inducedTensorMap (a.comp f) (b.comp g) = (inducedTensorMap a b).comp (inducedTensorMap f g) :=
 TensorProduct.map_comp a b f g

theorem inducedTensorAdd (f f' : V →ₗ[K] X) (g : W →ₗ[K] Y) :
 inducedTensorMap (f+f') g = inducedTensorMap f g + inducedTensorMap f' g := TensorProduct.map_add_left _ _ _

theorem inducedTensorSmul (a : K) (f : V →ₗ[K] X) (g : W →ₗ[K] Y) :
 inducedTensorMap (a • f) g = a • inducedTensorMap f g := TensorProduct.map_smul_left _ _ _

def tensorDirectSum : ((V × W) ⊗[K] X) ≃ₗ[K] ((V ⊗[K] X) × (W ⊗[K] X)) :=
 TensorProduct.prodLeft K K V W X

theorem tensorDirectSumPure (v : V) (w : W) (x : X) :
 tensorDirectSum ((v,w) ⊗ₜ[K] x) = (v ⊗ₜ[K] x,w ⊗ₜ[K] x) := TensorProduct.prodLeft_tmul _ _ _ _ _ _ _ _

def tensorAssociate : (V ⊗[K] (W ⊗[K] X)) ≃ₗ[K] ((V ⊗[K] W) ⊗[K] X) :=
 (TensorProduct.assoc K V W X).symm

theorem tensorAssociatePure (v : V) (w : W) (x : X) :
 tensorAssociate (v ⊗ₜ[K] (w ⊗ₜ[K] x)) = (v ⊗ₜ[K] w) ⊗ₜ[K] x := by simp [tensorAssociate]

def tensorSwap : V ⊗[K] W ≃ₗ[K] W ⊗[K] V := TensorProduct.comm K V W
theorem tensorSwapPure (v : V) (w : W) : tensorSwap (v ⊗ₜ[K] w) = w ⊗ₜ[K] v := TensorProduct.comm_tmul _ _ _ _ _

def tensorPowerPermute {ι : Type u} (σ : Equiv.Perm ι) :
 (⨂[K] _ : ι, V) ≃ₗ[K] (⨂[K] _ : ι, V) := PiTensorProduct.reindex K (fun _ : ι => V) σ

theorem tensorPowerPermutePure {ι : Type u} (σ : Equiv.Perm ι) (v : ι → V) :
 tensorPowerPermute σ (PiTensorProduct.tprod K v) = PiTensorProduct.tprod K (fun i => v (σ.symm i)) :=
 PiTensorProduct.reindex_tprod σ v

theorem tensorPowerLeftAction {ι : Type u} (σ τ : Equiv.Perm ι) (t : ⨂[K] _ : ι, V) :
 tensorPowerPermute τ (tensorPowerPermute σ t) = tensorPowerPermute (τ*σ) t := by
 exact PiTensorProduct.reindex_reindex σ τ t

def symmetricTensorSubmodule : Submodule K (V ⊗[K] V) :=
 LinearMap.ker ((tensorSwap (K:=K) (V:=V) (W:=V)).toLinearMap - LinearMap.id)
def skewTensorSubmodule : Submodule K (V ⊗[K] V) :=
 LinearMap.ker ((tensorSwap (K:=K) (V:=V) (W:=V)).toLinearMap + LinearMap.id)

theorem skewEqualsSymmetricCharTwo [CharP K 2] :
 skewTensorSubmodule (K:=K) (V:=V) = symmetricTensorSubmodule := by
 ext t
 simp only [skewTensorSubmodule, symmetricTensorSubmodule, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
 have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
 have hz : t + t = 0 := by
   rw [← two_smul K t, htwo, zero_smul]
 have h : -(t : V ⊗[K] V) = t := ((eq_neg_iff_add_eq_zero).2 hz).symm
 rw [sub_eq_add_neg, h]

theorem tensorSymmetricDecomposition (h : (2 : K) ≠ 0) (t : V ⊗[K] V) :
 (1/2 : K) • (t + tensorSwap t) + (1/2 : K) • (t - tensorSwap t) = t := by
 rw [← smul_add]
 have heq : t + tensorSwap t + (t - tensorSwap t) = (2 : K) • t := by
   rw [two_smul]; abel
 rw [heq, smul_smul, one_div_mul_cancel h, one_smul]

theorem symmetricSkewIntersection (h : (2 : K) ≠ 0) (t : V ⊗[K] V)
 (hs : tensorSwap t = t) (ha : tensorSwap t = -t) : t = 0 := by
 have ht : t + t = 0 := by
   calc t+t = (-t)+t := congrArg (fun z => z+t) (hs.symm.trans ha)
        _ = 0 := neg_add_cancel t
 have ht' : (2 : K) • t = 0 := by simpa [two_smul] using ht
 exact (smul_eq_zero.mp ht').resolve_left h

def usualExterior (n : ℕ) := ⋀[K]^n V

theorem exteriorDimension [FiniteDimensional K V] (n : ℕ) :
 finrank K (⋀[K]^n V) = (finrank K V).choose n := exteriorPower.finrank_eq K V n

theorem exteriorTopDimension [FiniteDimensional K V] :
 finrank K (⋀[K]^(finrank K V) V) = 1 := by simp [exteriorPower.finrank_eq]

theorem exteriorF2TwoDimension : finrank (ZMod 2) (⋀[ZMod 2]^2 (Fin 2 → ZMod 2)) = 1 := by
 simp [exteriorPower.finrank_eq, Module.finrank_pi]

theorem charTwoDiagonalSkewNonzero :
 ∃ t : (Fin 2 → ZMod 2) ⊗[ZMod 2] (Fin 2 → ZMod 2),
 tensorSwap t = -t ∧ t ≠ 0 := by
 let b := Pi.basisFun (ZMod 2) (Fin 2)
 let v := b 0
 refine ⟨v ⊗ₜ[ZMod 2] v, ?_, ?_⟩
 · rw [tensorSwapPure]
   have htwo : (2 : ZMod 2) = 0 := by decide
   have hz : v ⊗ₜ[ZMod 2] v + v ⊗ₜ[ZMod 2] v = 0 := by
     rw [← two_smul (ZMod 2), htwo, zero_smul]
   exact (eq_neg_iff_add_eq_zero).2 hz
 · intro h
   have he := congrArg (fun t => tensorFiniteSupport b b t (0,0)) h
   simp [tensorFiniteSupport, tensorBasis, b, v, Basis.tensorProduct_repr_tmul_apply] at he

theorem exteriorRepeatZero (v : V) : exteriorPower.ιMulti K 2 ![v,v] = 0 := by
 apply AlternatingMap.map_eq_zero_of_eq _ _ (i:=0) (j:=1)
 · rfl
 · decide

theorem exteriorMapPure (n : ℕ) (f : V →ₗ[K] W) (v : Fin n → V) :
 exteriorPower.map n f (exteriorPower.ιMulti K n v) = exteriorPower.ιMulti K n (f ∘ v) :=
 exteriorPower.map_apply_ιMulti f v

theorem alternatingBasisExpansion {n : ℕ} (b : Basis (Fin n) K V)
 (a : V [⋀^Fin n]→ₗ[K] W) (v : Fin n → V) : a v = b.det v • a b := by
 have h : a = b.det.smulRight (a b) := by
   refine b.ext_alternating fun i hi => ?_
   let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
   change a (b ∘ σ) = (b.det.smulRight (a b)) (b ∘ σ)
   simp [AlternatingMap.map_perm, Basis.det_self, Units.smul_def]
 exact congrArg (fun f => f v) h

theorem exteriorTopDeterminant {n : ℕ} (b : Basis (Fin n) K V) (f : V →ₗ[K] V) :
 exteriorPower.map n f = LinearMap.lsmul K (⋀[K]^n V) (LinearMap.det f) := by
 apply exteriorPower.linearMap_ext
 apply AlternatingMap.ext
 intro v
 change exteriorPower.map n f (exteriorPower.ιMulti K n v) = (LinearMap.det f) • exteriorPower.ιMulti K n v
 rw [exteriorPower.map_apply_ιMulti]
 rw [alternatingBasisExpansion b (exteriorPower.ιMulti K n) (f ∘ v), alternatingBasisExpansion b (exteriorPower.ιMulti K n) v]
 simp [Basis.det_comp, mul_smul]

end ILab.LinearAlgebra
