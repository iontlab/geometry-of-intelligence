import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Holstein §3.1–3.2, printed48–53. All spaces are over the same explicitly
specified field. Original typographical errors are retained in the source layer,
not asserted as mathematical identities here. Binary external sum is the product;
finite indexed DirectSum is connected to its function representation separately. -/
namespace ILab.LinearAlgebra
universe u v w
variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem vectorSpaceAxioms (a b : K) (v w : V) :
    (a+b) • v = a • v + b • v ∧ a • (v+w) = a • v + a • w ∧
    (a*b) • v = a • (b • v) ∧ (1:K) • v = v :=
  ⟨add_smul a b v, smul_add a v w, mul_smul a b v, one_smul K v⟩

@[instance_reducible]
def coordinateVectorSpace (K : Type*) [Field K] (n : ℕ) : Module K (Fin n → K) := inferInstance
@[instance_reducible]
def selfScalarVectorSpace (K : Type*) [Field K] : Module K K := inferInstance
@[instance_reducible]
def zeroVectorSpace (K : Type*) [Field K] : Module K (Fin 0 → K) := inferInstance
@[instance_reducible]
noncomputable def complexRealVectorSpace : Module ℝ ℂ := inferInstance
@[instance_reducible]
noncomputable def realRationalVectorSpace : Module ℚ ℝ := inferInstance
@[instance_reducible]
def functionVectorSpace (X : Type*) : Module K (X → V) := inferInstance
@[instance_reducible]
def sequenceVectorSpace : Module K (ℕ → K) := inferInstance
@[instance_reducible]
def outerPairVectorSpace (W : Type*) [AddCommGroup W] [Module K W] : Module K (V × W) := inferInstance

theorem functionVectorOperations {X : Type*} (f g : X → V) (a : K) (x : X) :
    (f+g) x = f x + g x ∧ (a • f) x = a • f x := ⟨rfl,rfl⟩
theorem outerPairOperations {W : Type*} [AddCommGroup W] [Module K W]
    (v v' : V) (w w' : W) (a : K) :
    (v,w)+(v',w')=(v+v',w+w') ∧ a • (v,w)=(a • v,a • w) := ⟨rfl,rfl⟩
theorem emptyCoordinateUnique (x : Fin 0 → K) : x = 0 := by ext i; exact Fin.elim0 i

/-- Source cancellation argument, rather than taking zero_smul as a new axiom. -/
theorem vectorZeroScalar (v : V) : (0:K) • v = 0 := by
  have h : (0:K) • v = (0:K) • v + (0:K) • v := by
    calc (0:K) • v = ((0:K)+0) • v := by rw [add_zero]
         _ = (0:K) • v + (0:K) • v := add_smul _ _ _
  exact (add_left_cancel (a:=(0:K) • v) (by simpa using h.symm))
theorem vectorScalarZero (a : K) : a • (0:V) = 0 := by
  have h : a • (0:V) = a • (0:V) + a • (0:V) := by
    calc a • (0:V) = a • ((0:V)+0) := by rw [add_zero]
         _ = a • (0:V) + a • (0:V) := smul_add _ _ _
  exact (add_left_cancel (a:=a • (0:V)) (by simpa using h.symm))
theorem vectorScalarZeroCriterion (a : K) (v : V) : a • v = 0 ↔ a=0 ∨ v=0 := by
  constructor
  · intro h
    by_cases ha : a=0
    · exact Or.inl ha
    · right
      calc v = a⁻¹ • (a • v) := (inv_smul_smul₀ ha v).symm
           _ = a⁻¹ • (0:V) := by rw [h]
           _ = 0 := vectorScalarZero a⁻¹
  · rintro (rfl | rfl)
    · exact vectorZeroScalar v
    · exact vectorScalarZero a
theorem vectorNegOneScalar (v : V) : (-1:K) • v = -v := by
  have h : (-1:K) • v + v = 0 := by
    calc (-1:K) • v + v = (-1:K) • v + (1:K) • v := by rw [one_smul]
         _ = ((-1:K)+1) • v := (add_smul _ _ _).symm
         _ = 0 := by simpa using vectorZeroScalar (K:=K) v
  exact eq_neg_of_add_eq_zero_left h

/-- UV1 is nonemptiness; zero membership is derived from it and UV3. -/
def subspaceFromAxioms (s : Set V) (hne : s.Nonempty)
    (ha : ∀ x∈s, ∀ y∈s, x+y∈s) (hs : ∀ a:K, ∀ x∈s, a • x∈s) : Submodule K V where
  carrier := s
  zero_mem' := by obtain ⟨x,hx⟩:=hne; simpa using hs 0 x hx
  add_mem' := fun hx hy => ha _ hx _ hy
  smul_mem' := fun a _ hx => hs a _ hx
theorem subspaceAxioms (U : Submodule K V) :
    (U:Set V).Nonempty ∧ (∀ x∈U, ∀ y∈U, x+y∈U) ∧ (∀ a:K, ∀ x∈U, a • x∈U) :=
  ⟨⟨0,U.zero_mem⟩,fun _ hx _ hy=>U.add_mem hx hy,fun a _ hx=>U.smul_mem a hx⟩
@[instance_reducible]
def inheritedSubspaceModule (U : Submodule K V) : Module K U := inferInstance
theorem subspaceZeroValue (U : Submodule K V) : ((0:U):V)=0 := rfl
theorem subspaceNegation (U : Submodule K V) {v : V} (hv : v∈U) : -v∈U := U.neg_mem hv

def complexRealAxis : Submodule ℝ ℂ where
  carrier := {z | z.im=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a z hz; simp_all
def complexImaginaryAxis : Submodule ℝ ℂ where
  carrier := {z | z.re=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a z hz; simp_all
theorem realAxisNotComplexClosed : (1:ℂ)∈complexRealAxis ∧ Complex.I*(1:ℂ)∉complexRealAxis := by
  simp [complexRealAxis]
def vectorGeneratedSubspace (v : V) : Submodule K V := Submodule.span K {v}
theorem generatedVectorMembership (v : V) (a : K) : a • v∈vectorGeneratedSubspace (K:=K) v :=
  Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

def arbitrarySubspaceIntersection {ι : Sort*} (U : ι → Submodule K V) : Submodule K V := ⨅ i, U i
theorem arbitraryIntersectionMembership {ι : Sort*} (U : ι → Submodule K V) (v : V) :
    v∈arbitrarySubspaceIntersection U ↔ ∀ i, v∈U i := Submodule.mem_iInf U
theorem emptySubspaceIntersection (U : Empty → Submodule K V) : arbitrarySubspaceIntersection U = ⊤ := by
  ext v; simp [arbitrarySubspaceIntersection]
theorem axesUnionNotAddClosed :
    (1:ℂ)∈(complexRealAxis:Set ℂ) ∪ complexImaginaryAxis ∧
    Complex.I∈(complexRealAxis:Set ℂ) ∪ complexImaginaryAxis ∧
    (1+Complex.I:ℂ)∉(complexRealAxis:Set ℂ) ∪ complexImaginaryAxis := by
  simp [complexRealAxis,complexImaginaryAxis]

/-- Finite internal sum, with an explicit tuple of source summands. -/
def finiteInnerSubspaceSum {r : ℕ} (U : Fin r → Submodule K V) : Submodule K V where
  carrier := {v | ∃ w:Fin r→V, (∀ i,w i∈U i) ∧ (∑ i,w i)=v}
  zero_mem' := ⟨0,by simp,by simp⟩
  add_mem' := by
    rintro x y ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨fun i=>a i+b i,fun i=>(U i).add_mem (ha i) (hb i),Finset.sum_add_distrib⟩
  smul_mem' := by
    rintro a x ⟨w,hw,rfl⟩
    exact ⟨fun i=>a • w i,fun i=>(U i).smul_mem a (hw i),(Finset.smul_sum).symm⟩
theorem finiteInnerSumContains {r : ℕ} (U : Fin r → Submodule K V) (i : Fin r) : U i ≤ finiteInnerSubspaceSum U := by
  intro x hx
  refine ⟨fun j=>if j=i then x else 0,?_,?_⟩
  · intro j; dsimp; split_ifs with h
    · simpa [h] using hx
    · exact (U j).zero_mem
  · simp
theorem finiteInnerSumMinimal {r : ℕ} (U : Fin r → Submodule K V) (T : Submodule K V)
    (h : ∀ i,U i≤T) : finiteInnerSubspaceSum U ≤ T := by
  rintro x ⟨w,hw,rfl⟩
  exact T.sum_mem (fun i _=>h i (hw i))
theorem finiteInnerSumIsSupremum {r : ℕ} (U : Fin r → Submodule K V) :
    finiteInnerSubspaceSum U = ⨆ i,U i := by
  apply le_antisymm
  · exact finiteInnerSumMinimal U _ (fun i=>le_iSup U i)
  · exact iSup_le (finiteInnerSumContains U)
theorem binarySubspaceSumMembership (U W : Submodule K V) (v : V) :
    v∈U⊔W ↔ ∃ x∈U, ∃ y∈W,x+y=v := Submodule.mem_sup

def subspaceSummation (U W : Submodule K V) : U × W →ₗ[K] V where
  toFun := fun p=>(p.1:V)+(p.2:V)
  map_add' := by intro a b; simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add]; abel
  map_smul' := by intro a p; simp
theorem subspaceSummationSurjective (U W : Submodule K V) (h : U⊔W=⊤) :
    Function.Surjective (subspaceSummation U W) := by
  intro v
  have hv : v∈U⊔W := by rw [h]; trivial
  obtain ⟨x,hx,y,hy,hxy⟩:= (binarySubspaceSumMembership U W v).mp hv
  exact ⟨(⟨x,hx⟩,⟨y,hy⟩),hxy⟩
theorem summationInjectiveIffTrivialIntersection (U W : Submodule K V) :
    Function.Injective (subspaceSummation U W) ↔ U⊓W=⊥ := by
  constructor
  · intro hi
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hp : ((⟨x,hx.1⟩,0):U×W)=(0,⟨x,hx.2⟩) := hi (by simp [subspaceSummation])
    exact congrArg (fun p:U×W=>(p.1:V)) hp
  · intro h p q he
    have hd : (p.1:V)-(q.1:V)∈U⊓W := by
      constructor
      · exact U.sub_mem p.1.property q.1.property
      · have ht : (p.1:V)-(q.1:V)=(q.2:V)-(p.2:V) := by
          change (p.1:V)+(p.2:V)=(q.1:V)+(q.2:V) at he
          exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using he)
        rw [ht]; exact W.sub_mem q.2.property p.2.property
    have hz : (p.1:V)-(q.1:V)=0 := (Submodule.eq_bot_iff _).mp h _ hd
    have h1 : p.1=q.1 := Subtype.ext (sub_eq_zero.mp hz)
    apply Prod.ext h1
    apply Subtype.ext
    change (p.1:V)+(p.2:V)=(q.1:V)+(q.2:V) at he
    rw [h1] at he
    exact add_left_cancel he
theorem uniqueSubspaceDecomposition (U W : Submodule K V) (hsum : U⊔W=⊤) :
    U⊓W=⊥ ↔ ∀ v:V, ∃! p:U×W,subspaceSummation U W p=v := by
  constructor
  · intro h v
    obtain ⟨p,hp⟩:=subspaceSummationSurjective U W hsum v
    exact ⟨p,hp,fun q hq=>(summationInjectiveIffTrivialIntersection U W).mpr h (hq.trans hp.symm)⟩
  · intro h
    apply (summationInjectiveIffTrivialIntersection U W).mp
    intro p q hpq
    obtain ⟨r,hr,hu⟩:=h (subspaceSummation U W p)
    exact (hu p rfl).trans (hu q hpq.symm).symm
def innerDirectSubspaceSum (U W : Submodule K V) : Prop := U⊔W=⊤ ∧ U⊓W=⊥
noncomputable def internalExternalSumEquivalence (U W : Submodule K V)
    (h : innerDirectSubspaceSum U W) : (U×W) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (subspaceSummation U W)
    ⟨(summationInjectiveIffTrivialIntersection U W).mpr h.2,subspaceSummationSurjective U W h.1⟩
noncomputable def finiteExternalDirectSumEquivalence {ι : Type*} [Fintype ι]
    (M : ι → Type*) [(i:ι)→AddCommGroup (M i)] [(i:ι)→Module K (M i)] :
    (DirectSum ι M) ≃ₗ[K] ((i:ι)→M i) := DirectSum.linearEquivFunOnFintype K ι M

theorem complexAxesDirectSum : innerDirectSubspaceSum complexRealAxis complexImaginaryAxis := by
  constructor
  · apply top_unique
    intro z _
    apply Submodule.mem_sup.mpr
    refine ⟨(z.re:ℂ),by simp [complexRealAxis],(z.im:ℂ)*Complex.I,by simp [complexImaginaryAxis],?_⟩
    exact Complex.re_add_im z
  · apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    apply Complex.ext
    · exact hz.2
    · exact hz.1
theorem repeatedImaginaryAxisNotDirect :
    ¬ innerDirectSubspaceSum complexImaginaryAxis complexImaginaryAxis := by
  intro h
  have hi : Complex.I∈complexImaginaryAxis⊓complexImaginaryAxis := by simp [complexImaginaryAxis]
  have hz := (Submodule.eq_bot_iff _).mp h.2 _ hi
  exact Complex.I_ne_zero hz

end ILab.LinearAlgebra
