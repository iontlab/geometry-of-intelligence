import ILab.LinearAlgebra.EigenvaluesDiagonalization
import ILab.LinearAlgebra.PolynomialTheory
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! Holstein §9.4. Eigenbases are finite bases with nonzero eigenvectors.
No algebraic closure assumption is added to the simultaneous theorem.
Finite-dimensionality is stated at every use of natural-valued finrank. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
local instance : DecidableEq K := Classical.decEq K

def HolsteinDiagonalizable (f : Module.End K V) : Prop :=
  ∃ n : ℕ, ∃ b : Basis (Fin n) K V, IsEigenbasis f b

def HolsteinSimultaneous (f g : Module.End K V) : Prop :=
  ∃ n : ℕ, ∃ b : Basis (Fin n) K V, IsEigenbasis f b ∧ IsEigenbasis g b

def InvariantSubspace (f : Module.End K V) (W : Submodule K V) : Prop :=
  ∀ v ∈ W, f v ∈ W

theorem invariantZero (f : Module.End K V) : InvariantSubspace f ⊥ := by
  intro v hv; have hz : v=0 := hv; subst v; simp

theorem invariantWhole (f : Module.End K V) : InvariantSubspace f ⊤ := by
  intro v hv; trivial

theorem invariantIntersection (f : Module.End K V) (U W : Submodule K V)
    (hU : InvariantSubspace f U) (hW : InvariantSubspace f W) :
    InvariantSubspace f (U ⊓ W) := by
  intro v hv; exact ⟨hU v hv.1,hW v hv.2⟩

theorem invariantSum (f : Module.End K V) (U W : Submodule K V)
    (hU : InvariantSubspace f U) (hW : InvariantSubspace f W) :
    InvariantSubspace f (U ⊔ W) := by
  intro v hv
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hU u hu) (hW w hw)

theorem commutePreservesEigenspace (f g : Module.End K V) (h : Commute f g) (a : K) :
    InvariantSubspace g (f.eigenspace a) := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  calc
    f (g v) = g (f v) := LinearMap.congr_fun h.eq v
    _ = a • g v := by rw [hv,map_smul]

theorem eigenspaceInvariant (f : Module.End K V) (a : K) :
    InvariantSubspace f (f.eigenspace a) := commutePreservesEigenspace f f (Commute.refl f) a

noncomputable def algebraicMultiplicity [FiniteDimensional K V] (f : Module.End K V) (a : K) : ℕ :=
  f.charpoly.rootMultiplicity a

theorem multiplicityBound [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    geometricMultiplicity f a ≤ algebraicMultiplicity f a :=
  LinearMap.finrank_eigenspace_le f a

theorem eigenMultiplicityBounds [FiniteDimensional K V] (f : Module.End K V) (a : K)
    (ha : f.HasEigenvalue a) :
    1 ≤ geometricMultiplicity f a ∧ geometricMultiplicity f a ≤ algebraicMultiplicity f a :=
  ⟨geometricMultiplicityPositive f a ha,multiplicityBound f a⟩

theorem eigenbasisMatrixDiagonal {n : ℕ} (f : Module.End K V)
    (b : Basis (Fin n) K V) (hb : IsEigenbasis f b) :
    ∃ d : Fin n → K, f=Matrix.toLin b b (Matrix.diagonal d) := by
  classical
  choose d hd using hb
  refine ⟨d,?_⟩
  apply b.ext
  intro i
  simpa [Matrix.diagonal] using (hd i).apply_eq_smul

theorem diagonalizableEigenspaceSpan (f : Module.End K V) (hf : HolsteinDiagonalizable f) :
    ⨆ a, f.eigenspace a = ⊤ := by
  obtain ⟨n,b,hb⟩ := hf
  apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
  intro i
  obtain ⟨a,ha⟩ := hb i
  exact Submodule.mem_iSup_of_mem a ha.1

theorem eigenspaceSpanDiagonalizable [FiniteDimensional K V] (f : Module.End K V)
    (hf : ⨆ a, f.eigenspace a = ⊤) : HolsteinDiagonalizable f := by
  classical
  let hi := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep hf
  let bases := fun a : K => Module.Free.chooseBasis K (f.eigenspace a)
  let b := hi.collectedBasis bases
  letI := FiniteDimensional.fintypeBasisIndex b
  refine ⟨Fintype.card _,b.reindex (Fintype.equivFin _),?_⟩
  intro i
  let j := (Fintype.equivFin _).symm i
  refine ⟨j.1,?_,(b.reindex (Fintype.equivFin _)).ne_zero i⟩
  simpa [b,j] using hi.collectedBasis_mem bases j

theorem diagonalizableIffEigenspaceDecomposition [FiniteDimensional K V] (f : Module.End K V) :
    HolsteinDiagonalizable f ↔ DirectSum.IsInternal f.eigenspace := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨fun h => ⟨f.eigenspaces_iSupIndep,diagonalizableEigenspaceSpan f h⟩,
    fun h => eigenspaceSpanDiagonalizable f h.2⟩

theorem diagonalizableGeneralizedEqualsOrdinary (f : Module.End K V)
    (hf : HolsteinDiagonalizable f) (a : K) : f.maxGenEigenspace a=f.eigenspace a := by
  obtain ⟨n,b,hb⟩ := hf
  obtain ⟨d,rfl⟩ := eigenbasisMatrixDiagonal f b hb
  exact Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace d b

theorem diagonalizableMultiplicities [FiniteDimensional K V] (f : Module.End K V)
    (hf : HolsteinDiagonalizable f) (a : K) :
    geometricMultiplicity f a=algebraicMultiplicity f a := by
  unfold geometricMultiplicity algebraicMultiplicity
  rw [← diagonalizableGeneralizedEqualsOrdinary f hf a]
  exact LinearMap.finrank_maxGenEigenspace_eq f a

theorem simultaneousImpliesCommute (f g : Module.End K V) (h : HolsteinSimultaneous f g) :
    Commute f g := by
  obtain ⟨n,b,hf,hg⟩ := h
  apply b.ext
  intro i
  obtain ⟨a,ha⟩ := hf i
  obtain ⟨c,hc⟩ := hg i
  change f (g (b i))=g (f (b i))
  rw [hc.apply_eq_smul,ha.apply_eq_smul,map_smul,map_smul,
    ha.apply_eq_smul,hc.apply_eq_smul,smul_smul,smul_smul,mul_comm]

theorem commutingDiagonalizableSimultaneous [FiniteDimensional K V]
    (f g : Module.End K V) (hf : HolsteinDiagonalizable f) (hg : HolsteinDiagonalizable g)
    (h : Commute f g) : HolsteinSimultaneous f g := by
  classical
  let F : Bool → Module.End K V := fun i => if i then g else f
  have hF (i : Bool) : HolsteinDiagonalizable (F i) := by cases i <;> assumption
  have hc (i j : Bool) : Commute (F i) (F j) := by
    cases i <;> cases j <;> simp only [F,Bool.false_eq_true,ite_false,ite_true]
    · exact Commute.refl f
    · exact h
    · exact h.symm
    · exact Commute.refl g
  have he (i : Bool) (a : K) : (F i).maxGenEigenspace a=(F i).eigenspace a :=
    diagonalizableGeneralizedEqualsOrdinary _ (hF i) a
  let A := fun χ : Bool → K => ⨅ i, (F i).maxGenEigenspace (χ i)
  have hA : iSup A=⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute F
      (fun i j _ => hc i j) (fun i => by simpa only [he] using diagonalizableEigenspaceSpan (F i) (hF i))
  have hi : iSupIndep A := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i))
  let internal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hA
  let bases := fun χ => Module.Free.chooseBasis K (A χ)
  let b := internal.collectedBasis bases
  letI := FiniteDimensional.fintypeBasisIndex b
  refine ⟨Fintype.card _,b.reindex (Fintype.equivFin _),?_,?_⟩
  all_goals
    intro i
    let j := (Fintype.equivFin _).symm i
    have hm := internal.collectedBasis_mem bases j
    change b j ∈ ⨅ l, (F l).maxGenEigenspace (j.1 l) at hm
    have hm' (l : Bool) : b j ∈ (F l).eigenspace (j.1 l) := by
      rw [← he]
      have hle : (⨅ l, (F l).maxGenEigenspace (j.1 l)) ≤ (F l).maxGenEigenspace (j.1 l) := iInf_le _ l
      exact hle hm
  · refine ⟨j.1 false,?_,(b.reindex (Fintype.equivFin _)).ne_zero i⟩
    simpa [F,j] using hm' false
  · refine ⟨j.1 true,?_,(b.reindex (Fintype.equivFin _)).ne_zero i⟩
    simpa [F,j] using hm' true

theorem simultaneousIffCommute [FiniteDimensional K V] (f g : Module.End K V)
    (hf : HolsteinDiagonalizable f) (hg : HolsteinDiagonalizable g) :
    HolsteinSimultaneous f g ↔ Commute f g :=
  ⟨simultaneousImpliesCommute f g,commutingDiagonalizableSimultaneous f g hf hg⟩

theorem traceSumRoots [FiniteDimensional K V] (f : Module.End K V) (h : f.charpoly.Splits) :
    f.trace K V=f.charpoly.roots.sum := Module.End.trace_eq_sum_roots_charpoly_of_splits h

theorem diagonalizableCharpolySplits [FiniteDimensional K V] (f : Module.End K V)
    (hf : HolsteinDiagonalizable f) : f.charpoly.Splits := by
  classical
  obtain ⟨n,b,hb⟩ := hf
  obtain ⟨d,rfl⟩ := eigenbasisMatrixDiagonal f b hb
  rw [← LinearMap.charpoly_toMatrix _ b,LinearMap.toMatrix_toLin,Matrix.charpoly_diagonal]
  exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C (d i)

theorem eigenspaceFiniteSumDimension [FiniteDimensional K V] (f : Module.End K V) (s : Finset K) :
    Module.finrank K ↥(s.sup f.eigenspace)=∑ a ∈ s,geometricMultiplicity f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [geometricMultiplicity]
  | @insert a s ha ih =>
    have hd : Disjoint (f.eigenspace a) (s.sup f.eigenspace) := by
      simpa only [Finset.sup_eq_iSup,Finset.mem_coe] using f.eigenspaces_iSupIndep.disjoint_biSup (show a ∉ (s:Set K) from ha)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace a) (s.sup f.eigenspace)
    rw [hd.eq_bot,finrank_bot,add_zero] at hdim
    rw [Finset.sup_insert,Finset.sum_insert ha,← ih]
    exact hdim

theorem eigenspaceRootSum [FiniteDimensional K V] (f : Module.End K V) :
    f.charpoly.roots.toFinset.sup f.eigenspace=⨆ a,f.eigenspace a := by
  classical
  apply le_antisymm
  · exact Finset.sup_le fun a _ => le_iSup f.eigenspace a
  · refine iSup_le fun a => ?_
    by_cases ha : a ∈ f.charpoly.roots.toFinset
    · exact Finset.le_sup ha
    · have hz : f.eigenspace a=⊥ := by
        by_contra hn
        apply ha
        exact Multiset.mem_toFinset.mpr <| (Polynomial.mem_roots f.charpoly_monic.ne_zero).mpr <|
          (f.hasEigenvalue_iff_isRoot_charpoly a).mp hn
      rw [hz];exact bot_le

theorem diagonalizableIffDimensionSum [FiniteDimensional K V] (f : Module.End K V) :
    HolsteinDiagonalizable f ↔
      (∑ a ∈ f.charpoly.roots.toFinset,geometricMultiplicity f a)=Module.finrank K V := by
  classical
  rw [← eigenspaceFiniteSumDimension,eigenspaceRootSum]
  constructor
  · intro h;rw [diagonalizableEigenspaceSpan f h,finrank_top]
  · intro h
    apply eigenspaceSpanDiagonalizable
    exact Submodule.eq_top_of_finrank_eq h

theorem diagonalizabilityCriterion [FiniteDimensional K V] (f : Module.End K V) :
    HolsteinDiagonalizable f ↔ f.charpoly.Splits ∧
      ∀ a, f.HasEigenvalue a → geometricMultiplicity f a=algebraicMultiplicity f a := by
  classical
  constructor
  · intro h;exact ⟨diagonalizableCharpolySplits f h,fun a _ => diagonalizableMultiplicities f h a⟩
  · rintro ⟨hs,hm⟩
    apply (diagonalizableIffDimensionSum f).mpr
    calc
      (∑ a ∈ f.charpoly.roots.toFinset,geometricMultiplicity f a) =
          ∑ a ∈ f.charpoly.roots.toFinset,algebraicMultiplicity f a := by
        apply Finset.sum_congr rfl
        intro a ha
        apply hm a
        exact (f.hasEigenvalue_iff_isRoot_charpoly a).mpr <|
          (Polynomial.mem_roots f.charpoly_monic.ne_zero).mp (Multiset.mem_toFinset.mp ha)
      _ = f.charpoly.roots.card := by
        simp only [algebraicMultiplicity,← Polynomial.count_roots]
        exact Multiset.toFinset_sum_count_eq _
      _ = Module.finrank K V := hs.natDegree_eq_card_roots.symm.trans (LinearMap.charpoly_natDegree f)

section CommutativeRing
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
theorem ringDeterminantMultiplicative (A B : Matrix n n R) : (A*B).det=A.det*B.det := Matrix.det_mul A B
theorem formalCharacteristicPolynomial (A : Matrix n n R) :
    A.charpoly=Matrix.det (Matrix.charmatrix A) := rfl
theorem characteristicPolynomialRingSimilarity (S : (Matrix n n R)ˣ) (A : Matrix n n R) :
    ((S:Matrix n n R)*A*((S:Matrix n n R)⁻¹)).charpoly=A.charpoly := Matrix.charpoly_units_conj S A
theorem characteristicBaseExtension {S : Type*} [CommRing S] (i : R →+* S) (A : Matrix n n R) :
    (A.map i).charpoly=A.charpoly.map i := Matrix.charpoly_map A i
end CommutativeRing

def jordanParameterMatrix (a : K) : Matrix (Fin 2) (Fin 2) K := !![a,1;0,a]
theorem jordanParameterCharpoly (a : K) : (jordanParameterMatrix a).charpoly=(X-C a)^2 := by
  simp [Matrix.charpoly,Matrix.charmatrix,Matrix.det_fin_two,jordanParameterMatrix,pow_two]

theorem jordanParameterEigenspace (a : K) (v : Fin 2 → K) :
    (jordanParameterMatrix a).mulVec v=a • v ↔ v 1=0 := by
  simp [jordanParameterMatrix,dotProduct,Fin.sum_univ_two,
    funext_iff,Fin.forall_fin_two]

theorem diagonalMatrixDiagonalizable {n : ℕ} (d : Fin n → K) :
    HolsteinDiagonalizable (Matrix.diagonal d).toLin' := by
  refine ⟨n,Pi.basisFun K (Fin n),?_⟩
  intro i;exact ⟨d i,hasEigenvector_toLin'_diagonal d i⟩

theorem finiteTwoIdentityDiagonalizable :
    HolsteinDiagonalizable (Matrix.diagonal (fun _ : Fin 2 => (1:ZMod 2))).toLin' :=
  diagonalMatrixDiagonalizable _

theorem finiteTwoJordanPolynomial :
    (jordanParameterMatrix (1:ZMod 2)).charpoly=(X-1)^2 := by
  simpa using jordanParameterCharpoly (1:ZMod 2)

theorem matrixDiagonalizabilityCriterion {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    HolsteinDiagonalizable A.toLin' ↔ A.toLin'.charpoly.Splits ∧
      ∀ a, Module.End.HasEigenvalue A.toLin' a →
        geometricMultiplicity A.toLin' a=algebraicMultiplicity A.toLin' a :=
  diagonalizabilityCriterion A.toLin'

end ILab.LinearAlgebra
