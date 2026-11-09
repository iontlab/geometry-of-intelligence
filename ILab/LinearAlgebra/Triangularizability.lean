import ILab.LinearAlgebra.Diagonalizability
import ILab.LinearAlgebra.CoordinateChanges
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
namespace ILab.LinearAlgebra
open Module Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
local instance triangularizationDecidableEq : DecidableEq K := Classical.decEq K

/-- Holstein's complete flag: all dimensions, both endpoints, and nesting. -/
structure HolsteinFlag (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (n : ℕ) where
  space : Fin (n+1) → Submodule K V
  monotone : Monotone space
  zero : space 0 = ⊥
  last : space (Fin.last n) = ⊤
  dimension : ∀ r, finrank K (space r) = r.val

def InvariantFlag {n : ℕ} (f : Module.End K V) (F : HolsteinFlag K V n) : Prop :=
  ∀ r, InvariantSubspace f (F.space r)

def HolsteinTriangularizable (f : Module.End K V) : Prop :=
  ∃ n : ℕ, ∃ b : Basis (Fin n) K V, (LinearMap.toMatrix b b f).IsUpperTriangular

def MatrixTriangularizable {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ S Si : Matrix (Fin n) (Fin n) K,
    S*Si=1 ∧ Si*S=1 ∧ (S*A*Si).IsUpperTriangular

theorem basisFlagDimension {n : ℕ} (b : Basis (Fin n) K V) (r : Fin (n+1)) :
    finrank K (b.flag r) = r.val := by
  classical
  let I := {i : Fin n // i.castSucc < r}
  let e : I ≃ Fin r.val :=
    { toFun := fun i => ⟨i.val.val, i.property⟩
      invFun := fun i => ⟨⟨i.val, by have := r.isLt; have := i.isLt; omega⟩,i.isLt⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  have hspan : Submodule.span K (Set.range (fun i : I => b i.val)) = b.flag r := by
    unfold Basis.flag
    congr 1
    ext y
    simp only [Set.mem_range,Set.mem_image,Set.mem_setOf_eq]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  rw [← hspan]
  change finrank K (Submodule.span K (Set.range (b ∘ (Subtype.val : I → Fin n)))) = r.val
  rw [finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)]
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

def basisCompleteFlag {n : ℕ} (b : Basis (Fin n) K V) : HolsteinFlag K V n where
  space := b.flag
  monotone := b.flag_mono
  zero := b.flag_zero
  last := b.flag_last
  dimension := basisFlagDimension b

theorem basisFlagInvariantIffUpper {n : ℕ} (f : Module.End K V) (b : Basis (Fin n) K V) :
    InvariantFlag f (basisCompleteFlag b) ↔ (LinearMap.toMatrix b b f).IsUpperTriangular := by
  constructor
  · intro h i j hij
    have hj : b j ∈ b.flag j.succ := b.self_mem_flag (by simp)
    have hx := h j.succ (b j) hj
    have hc := (b.mem_flag_iff_repr_eq_zero.mp hx) i (by change j.val+1 ≤ i.val; exact hij)
    simpa [LinearMap.toMatrix_apply] using hc
  · intro h r
    have hm : b.flag r ≤ (b.flag r).comap f := by
      apply b.flag_le_iff.mpr
      intro j hj
      change f (b j) ∈ b.flag r
      apply b.mem_flag_iff_repr_eq_zero.mpr
      intro i hi
      change j.val < r.val at hj
      change r.val ≤ i.val at hi
      simpa [LinearMap.toMatrix_apply] using h (i:=i) (j:=j) (show j < i from Nat.lt_of_lt_of_le hj hi)
    exact hm

theorem triangularizableHasInvariantFlag (f : Module.End K V)
    (h : HolsteinTriangularizable f) :
    ∃ n, ∃ F : HolsteinFlag K V n, InvariantFlag f F := by
  obtain ⟨n,b,hb⟩ := h
  exact ⟨n,basisCompleteFlag b,(basisFlagInvariantIffUpper f b).mpr hb⟩

theorem upperCharacteristicPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : A.IsUpperTriangular) : A.charpoly=∏ i, (X-C (A i i)) :=
  Matrix.charpoly_of_isUpperTriangular A h

theorem upperCharacteristicSplits {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : A.IsUpperTriangular) : A.charpoly.Splits := by
  rw [upperCharacteristicPolynomial A h]
  exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)

theorem upperDiagonalRoots {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : A.IsUpperTriangular) :
    A.charpoly.roots=(Finset.univ : Finset (Fin n)).val.map (fun i => A i i) := by
  rw [upperCharacteristicPolynomial A h]
  simpa only [Finset.prod_eq_multiset_prod,Multiset.map_map,Function.comp_def] using
    Polynomial.roots_multiset_prod_X_sub_C ((Finset.univ : Finset (Fin n)).val.map (fun i => A i i))

theorem upperDiagonalMultiplicity {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : A.IsUpperTriangular) (a : K) :
    A.charpoly.rootMultiplicity a = ((Finset.univ : Finset (Fin n)).val.map (fun i => A i i)).count a := by
  rw [← Polynomial.count_roots,upperDiagonalRoots A h]

theorem triangularizableCharpolySplits [FiniteDimensional K V] (f : Module.End K V)
    (h : HolsteinTriangularizable f) : f.charpoly.Splits := by
  obtain ⟨n,b,hb⟩ := h
  rw [← LinearMap.charpoly_toMatrix f b]
  exact upperCharacteristicSplits _ hb

theorem diagonalizableTriangularizable (f : Module.End K V)
    (h : HolsteinDiagonalizable f) : HolsteinTriangularizable f := by
  obtain ⟨n,b,hb⟩ := h
  obtain ⟨d,hd⟩ := eigenbasisMatrixDiagonal f b hb
  refine ⟨n,b,?_⟩
  rw [hd,LinearMap.toMatrix_toLin]
  intro i j hij
  change j < i at hij
  simp [Matrix.diagonal_apply,ne_of_gt hij]

theorem blockCharacteristicFactor {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (D : Matrix n n K) :
    (Matrix.fromBlocks A B 0 D).charpoly=A.charpoly*D.charpoly :=
  Matrix.charpoly_fromBlocks_zero₂₁ A B D

theorem blockCharacteristicDivisibility {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (D : Matrix n n K) :
    A.charpoly ∣ (Matrix.fromBlocks A B 0 D).charpoly := by
  rw [blockCharacteristicFactor]; exact dvd_mul_right _ _

/-- First index versus the remaining indices, with the first basis vector fixed. -/
def triangularHeadIndex (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by intro x; cases x with | inl x => cases x; rfl | inr x => rfl
  right_inv := by intro x; refine Fin.cases ?_ (fun i => ?_) x <;> rfl

theorem headBlockCharpoly {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (h : ∀ i : Fin n, A i.succ 0=0) :
    A.charpoly=(X-C (A 0 0))*(A.submatrix Fin.succ Fin.succ).charpoly := by
  let e := triangularHeadIndex n
  have ha : Matrix.reindex e.symm e.symm A = Matrix.fromBlocks
      (fun (_ _:Unit) => A 0 0) (fun (_:Unit) j => A 0 j.succ) 0
      (A.submatrix Fin.succ Fin.succ) := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i => cases j with
      | inl j => simpa [Matrix.reindex,Matrix.submatrix,e,triangularHeadIndex,Matrix.fromBlocks] using h i
      | inr j => rfl
  have hc := Matrix.charpoly_reindex e.symm A
  rw [ha] at hc
  have hh : Matrix.charpoly (fun (_ _:Unit) => A 0 0)=X-C (A 0 0) := by
    simp [Matrix.charpoly,Matrix.charmatrix,Matrix.det_unique,RingHom.mapMatrix_apply]
    rfl
  calc
    A.charpoly = (Matrix.fromBlocks (fun (_ _:Unit) => A 0 0)
        (fun (_:Unit) j => A 0 j.succ) 0 (A.submatrix Fin.succ Fin.succ)).charpoly := hc.symm
    _ = Matrix.charpoly (fun (_ _:Unit) => A 0 0) *
        (A.submatrix Fin.succ Fin.succ).charpoly :=
      Matrix.charpoly_fromBlocks_zero₂₁ _ _ _
    _ = _ := by rw [hh]

/-- Coordinate split used in the inductive change of basis. -/
def triangularHeadTail (n : ℕ) : (Fin (n+1) → K) ≃ₗ[K] K × (Fin n → K) where
  toFun v := (v 0,fun i => v i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv := by intro v; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by intro p; cases p; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem eigenvectorHeadBasis [FiniteDimensional K V] (v : V) (hv : v ≠ 0) :
    ∃ n : ℕ, ∃ b : Basis (Fin (n+1)) K V, b 0=v := by
  classical
  have hs : LinearIndepOn K id {v} := by
    simpa using (linearIndepOn_singleton_iff (R:=K) (v:=id) (i:=v)).mpr hv
  let b0 := Basis.extend hs
  letI := FiniteDimensional.fintypeBasisIndex b0
  let i : hs.extend (Set.subset_univ _) := ⟨v,hs.subset_extend _ (by simp)⟩
  let e := Fintype.equivFin (hs.extend (Set.subset_univ _))
  have hpos : 0 < Fintype.card (hs.extend (Set.subset_univ _)) := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let e' := e.trans (finCongr hn)
  let b1 := b0.reindex e'
  let b := b1.reindex (Equiv.swap (e' i) 0)
  refine ⟨n,b,?_⟩
  simp [b,b1,Basis.reindex_apply,b0,i,e']

def triangularCoordinates {n : ℕ} (b : Basis (Fin n) K (Fin n → K)) :
    (Fin (n+1) → K) ≃ₗ[K] (Fin (n+1) → K) where
  toFun v := Fin.cons (v 0) (b.equivFun (fun i => v i.succ))
  invFun v := Fin.cons (v 0) (b.equivFun.symm (fun i => v i.succ))
  left_inv := by
    intro v; ext i; refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [Fin.cons_zero,Fin.cons_succ,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  right_inv := by
    intro v; ext i; refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [Fin.cons_zero,Fin.cons_succ,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  map_add' := by
    intro x y; ext i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change b.equivFun ((fun i => x i.succ)+(fun i => y i.succ)) j = _
      simp only [map_add,Pi.add_apply,Fin.cons_succ]
  map_smul' := by
    intro c x; ext i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change b.equivFun (c • (fun i => x i.succ)) j = _
      simp only [map_smul,Pi.smul_apply,RingHom.id_apply,Fin.cons_succ]

def triangularLiftBasis {n : ℕ} (b : Basis (Fin n) K (Fin n → K)) :
    Basis (Fin (n+1)) K (Fin (n+1) → K) := Basis.ofEquivFun (triangularCoordinates b)

theorem triangularLiftBasisZero {n : ℕ} (b : Basis (Fin n) K (Fin n → K)) :
    triangularLiftBasis b 0=Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [triangularLiftBasis,Basis.coe_ofEquivFun,triangularCoordinates,Pi.single_apply]

theorem triangularLiftBasisSucc {n : ℕ} (b : Basis (Fin n) K (Fin n → K)) (j : Fin n) :
    triangularLiftBasis b j.succ=Fin.cons 0 (b j) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [triangularLiftBasis,Basis.coe_ofEquivFun,triangularCoordinates,Pi.single_apply,
      Basis.equivFun_symm_apply]

theorem triangularLiftUpper {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (hA : ∀ i : Fin n, A i.succ 0=0)
    (b : Basis (Fin n) K (Fin n → K))
    (hb : (LinearMap.toMatrix b b (Matrix.toLin' (A.submatrix Fin.succ Fin.succ))).IsUpperTriangular) :
    (LinearMap.toMatrix (triangularLiftBasis b) (triangularLiftBasis b) (Matrix.toLin' A)).IsUpperTriangular := by
  intro i
  refine Fin.cases ?_ (fun i' => ?_) i
  · intro j hij; exact False.elim (Fin.not_lt_zero j hij)
  · intro j
    refine Fin.cases ?_ (fun j' => ?_) j
    · intro hij
      rw [LinearMap.toMatrix_apply,triangularLiftBasisZero]
      simp [triangularLiftBasis,Basis.ofEquivFun_repr_apply,triangularCoordinates,
        Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hA,Pi.single_apply]
      change (b.repr (0 : Fin n → K)) i' = 0
      simp
    · intro hij
      have ht : (fun i' => A.mulVec (Fin.cons 0 (b j')) i'.succ) =
          (A.submatrix Fin.succ Fin.succ).mulVec (b j') := by
        ext k
        simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      have hh := hb (i:=i') (j:=j') (by simpa using hij)
      rw [LinearMap.toMatrix_apply,triangularLiftBasisSucc]
      simpa [triangularLiftBasis,Basis.ofEquivFun_repr_apply,triangularCoordinates,
        Matrix.toLin'_apply,ht,Basis.equivFun_apply,LinearMap.toMatrix_apply] using hh

theorem triangularCoordinateMap {n : ℕ} (f : Module.End K V) (b : Basis (Fin n) K V) :
    Matrix.toLin' (LinearMap.toMatrix b b f)=b.equivFun.conj f := by
  apply LinearMap.ext
  intro x
  apply _root_.funext
  intro i
  have h := congrFun (f.toMatrix_mulVec_repr b b (b.equivFun.symm x)) i
  change (LinearMap.toMatrix b b f).mulVec (b.equivFun (b.equivFun.symm x)) i =
    b.equivFun (f (b.equivFun.symm x)) i at h
  simpa only [Matrix.toLin'_apply,LinearEquiv.conj_apply,LinearEquiv.apply_symm_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe] using h

theorem triangularTransportBasis {n : ℕ} (f : Module.End K V) (b : Basis (Fin n) K V)
    (c : Basis (Fin n) K (Fin n → K)) :
    LinearMap.toMatrix (c.map b.equivFun.symm) (c.map b.equivFun.symm) f =
      LinearMap.toMatrix c c (Matrix.toLin' (LinearMap.toMatrix b b f)) := by
  rw [triangularCoordinateMap]
  rfl

set_option maxHeartbeats 800000 in
/-- Full finite-dimensional criterion over any field, by dimension induction.
No algebraic closure assumption and no distinct-eigenvalue assumption. -/
theorem matrixCharpolySplitsTriangularizable (N : ℕ) (A0 : Matrix (Fin N) (Fin N) K)
    (hf0 : A0.charpoly.Splits) : HolsteinTriangularizable (Matrix.toLin' A0) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    let f : Module.End K (Fin N → K) := Matrix.toLin' A0
    have hf : f.charpoly.Splits := by simpa [f] using hf0
    by_cases hz : N=0
    · subst N
      refine ⟨0,Pi.basisFun K (Fin 0),?_⟩
      intro i; exact Fin.elim0 i
    · have hdeg : f.charpoly.degree ≠ 0 := by
        intro he
        have hn := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq he)
        rw [LinearMap.charpoly_natDegree] at hn
        simp only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,mul_one] at hn
        exact hz hn
      obtain ⟨a,ha⟩ := hf.exists_eval_eq_zero hdeg
      have hev : f.HasEigenvalue a := (Module.End.hasEigenvalue_iff_isRoot_charpoly f a).mpr ha
      obtain ⟨v,hv⟩ := hev.exists_hasEigenvector
      obtain ⟨n,b,hb⟩ := eigenvectorHeadBasis (K:=K) v hv.2
      let A := LinearMap.toMatrix b b f
      have hcol : ∀ i : Fin n, A i.succ 0=0 := by
        intro i
        have heq : f v=a • v := Module.End.mem_eigenspace_iff.mp hv.1
        dsimp only [A]
        rw [LinearMap.toMatrix_apply]
        rw [hb,heq,← hb,map_smul]
        simp
      let R := A.submatrix Fin.succ Fin.succ
      let g := Matrix.toLin' R
      have hfactor : f.charpoly=(X-C (A 0 0))*R.charpoly := by
        rw [← LinearMap.charpoly_toMatrix f b]
        exact headBlockCharpoly A hcol
      have hsplit : g.charpoly.Splits := by
        rw [Matrix.charpoly_toLin']
        apply hf.of_dvd (LinearMap.charpoly_monic f).ne_zero
        exact ⟨X-C (A 0 0),by rw [hfactor]; ring⟩
      have hdim : N=n+1 := by simpa using finrank_eq_card_basis b
      have hn : n<N := by omega
      have hrsplit : R.charpoly.Splits := by simpa [g] using hsplit
      obtain ⟨m,c,hc⟩ := ih n hn R hrsplit
      have hm : m=n := by have h := finrank_eq_card_basis c; simpa using h.symm
      subst m
      let lifted := triangularLiftBasis c
      refine ⟨n+1,lifted.map b.equivFun.symm,?_⟩
      rw [triangularTransportBasis]
      exact triangularLiftUpper A hcol c hc

theorem charpolySplitsTriangularizable [FiniteDimensional K V] (f : Module.End K V)
    (hf : f.charpoly.Splits) : HolsteinTriangularizable f := by
  classical
  let b := Module.finBasis K V
  let A := LinearMap.toMatrix b b f
  have ha : A.charpoly.Splits := by simpa [A] using hf
  obtain ⟨m,c,hc⟩ := matrixCharpolySplitsTriangularizable _ A ha
  have hm : m=finrank K V := by have h := finrank_eq_card_basis c; simpa using h.symm
  subst m
  refine ⟨finrank K V,c.map b.equivFun.symm,?_⟩
  rw [triangularTransportBasis]
  exact hc

theorem triangularizabilityCriterion [FiniteDimensional K V] (f : Module.End K V) :
    HolsteinTriangularizable f ↔ f.charpoly.Splits :=
  ⟨triangularizableCharpolySplits f,charpolySplitsTriangularizable f⟩

theorem algebraicallyClosedTriangularizable [FiniteDimensional K V] [IsAlgClosed K]
    (f : Module.End K V) : HolsteinTriangularizable f :=
  charpolySplitsTriangularizable f (IsAlgClosed.splits _)

theorem complexEndomorphismTriangularizable {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) : HolsteinTriangularizable f :=
  algebraicallyClosedTriangularizable f

theorem invariantRestrictionCharpolyDivides [FiniteDimensional K V]
    (f : Module.End K V) (W : Submodule K V) (hW : InvariantSubspace f W) :
    (f.restrict hW).charpoly ∣ f.charpoly := by
  classical
  obtain ⟨N,hN⟩ := Submodule.exists_isCompl W
  let e := Submodule.prodEquivOfIsCompl W N hN
  let g := e.symm.conj f
  let fw := f.restrict hW
  let bW := Module.finBasis K W
  let bN := Module.finBasis K N
  let b := bW.prod bN
  let A := LinearMap.toMatrix b b g
  have hg (w : W) : g (w,0)=(fw w,0) := by
    apply e.injective
    change e (e.symm (f (e (w,0))))=e (fw w,0)
    rw [e.apply_symm_apply]
    change f ((w:V)+0)=(fw w:V)+0
    simp [fw]
    rfl
  have h11 : A.toBlocks₁₁=LinearMap.toMatrix bW bW fw := by
    ext i j
    simp [A,Matrix.toBlocks₁₁,LinearMap.toMatrix_apply,b,Basis.prod_apply,hg]
  have h21 : A.toBlocks₂₁=0 := by
    ext i j
    simp [A,Matrix.toBlocks₂₁,LinearMap.toMatrix_apply,b,Basis.prod_apply,hg]
  have hc : g.charpoly=A.charpoly := (LinearMap.charpoly_toMatrix g b).symm
  have hmatrix : A=Matrix.fromBlocks (LinearMap.toMatrix bW bW fw) A.toBlocks₁₂ 0 A.toBlocks₂₂ := by
    rw [← h11,← h21]; exact (Matrix.fromBlocks_toBlocks A).symm
  have hfactor : f.charpoly=fw.charpoly*A.toBlocks₂₂.charpoly := by
    calc
      f.charpoly = g.charpoly := (e.symm.charpoly_conj f).symm
      _ = A.charpoly := hc
      _ = (Matrix.fromBlocks (LinearMap.toMatrix bW bW fw) A.toBlocks₁₂ 0 A.toBlocks₂₂).charpoly := congrArg Matrix.charpoly hmatrix
      _ = _ := by rw [Matrix.charpoly_fromBlocks_zero₂₁,LinearMap.charpoly_toMatrix]
  exact ⟨A.toBlocks₂₂.charpoly,hfactor⟩

def flagInitialSegment {n : ℕ} (F : HolsteinFlag K V (n+1)) :
    HolsteinFlag K (F.space ⟨n,by omega⟩) n where
  space r := (F.space r.castSucc).comap (F.space ⟨n,by omega⟩).subtype
  monotone := by
    intro a b hab
    exact Submodule.comap_mono (F.monotone (by simpa using hab))
  zero := by simp [F.zero]
  last := by
    change (F.space ⟨n,by omega⟩).comap (F.space ⟨n,by omega⟩).subtype=⊤
    exact Submodule.comap_subtype_self _
  dimension r := by
    have hle : F.space r.castSucc ≤ F.space ⟨n,by omega⟩ :=
      F.monotone (by change r.val ≤ n; omega)
    have hd := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
    exact hd.trans (F.dimension r.castSucc)

theorem invariantFlagInitialSegment {n : ℕ} (f : Module.End K V)
    (F : HolsteinFlag K V (n+1)) (hF : InvariantFlag f F) :
    InvariantFlag (f.restrict (hF ⟨n,by omega⟩)) (flagInitialSegment F) := by
  intro r x hx
  exact hF r.castSucc x.val hx

set_option maxHeartbeats 800000 in
theorem invariantFlagCharpolySplits [FiniteDimensional K V] (n : ℕ)
    (f : Module.End K V) (F : HolsteinFlag K V n) (hF : InvariantFlag f F) :
    f.charpoly.Splits := by
  classical
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    have hdim : finrank K V=n := by
      have h := F.dimension (Fin.last n)
      rw [F.last,finrank_top] at h
      exact h
    cases n with
    | zero =>
      apply Polynomial.Splits.of_natDegree_eq_zero
      rw [LinearMap.charpoly_natDegree,hdim]
    | succ m =>
      let W := F.space ⟨m,by omega⟩
      have hW : InvariantSubspace f W := hF _
      let g : Module.End K W := f.restrict hW
      have hg : g.charpoly.Splits :=
        ih m (Nat.lt_succ_self m) g (flagInitialSegment F) (invariantFlagInitialSegment f F hF)
      obtain ⟨q,hq⟩ := invariantRestrictionCharpolyDivides f W hW
      have hqne : q≠0 := by
        intro hz; rw [hz,mul_zero] at hq
        exact (LinearMap.charpoly_monic f).ne_zero hq
      have hdimW : finrank K W=m := F.dimension _
      have hd := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul (LinearMap.charpoly_monic g).ne_zero hqne,
        LinearMap.charpoly_natDegree,LinearMap.charpoly_natDegree,hdim,hdimW] at hd
      have hqdeg : q.natDegree≤1 := by omega
      rw [hq]
      exact hg.mul (Polynomial.Splits.of_degree_le_one (Polynomial.degree_le_of_natDegree_le hqdeg))

theorem invariantFlagIffTriangularizable [FiniteDimensional K V] (f : Module.End K V) :
    (∃ n, ∃ F : HolsteinFlag K V n, InvariantFlag f F) ↔ HolsteinTriangularizable f := by
  constructor
  · rintro ⟨n,F,hF⟩
    exact charpolySplitsTriangularizable f (invariantFlagCharpolySplits n f F hF)
  · exact triangularizableHasInvariantFlag f

theorem matrixTriangularizabilityCriterion {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    MatrixTriangularizable A ↔ A.charpoly.Splits := by
  constructor
  · rintro ⟨S,Si,hS,hSi,hT⟩
    have hcp : (S*A*Si).charpoly=A.charpoly := by
      rw [Matrix.charpoly_mul_comm (S*A) Si,← Matrix.mul_assoc,hSi,Matrix.one_mul]
    have h := upperCharacteristicSplits (S*A*Si) hT
    rwa [hcp] at h
  · intro h
    obtain ⟨m,b,hb⟩ := matrixCharpolySplitsTriangularizable n A h
    have hm : m=n := by have hd := finrank_eq_card_basis b; simpa using hd.symm
    subst m
    let std := Pi.basisFun K (Fin n)
    let S := coordinateChange std b
    let Si := coordinateChange b std
    have hi := coordinateChangeInverseProducts std b
    refine ⟨S,Si,hi.1,hi.2,?_⟩
    have ht := matrixChangeFormulaReverse std b std b (Matrix.toLin' A)
    have heq : LinearMap.toMatrix b b (Matrix.toLin' A)=S*A*Si := by
      simpa [matrixRepresentation,Matrix.toLin_eq_toLin',std,S,Si] using ht
    rwa [← heq]

theorem complexMatrixTriangularizable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    MatrixTriangularizable A :=
  (matrixTriangularizabilityCriterion A).mpr (IsAlgClosed.splits _)

def originalTriangularMatrix : Matrix (Fin 3) (Fin 3) ℚ := !![3,4,3;-1,0,-1;1,2,3]
def originalTriangularS1 : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,0;1,1,0;-1,0,1]
def originalTriangularS1i : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,0;-1,1,0;1,0,1]
def originalTriangularS2 : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,0;0,1,0;0,1,1]
def originalTriangularS2i : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,0;0,1,0;0,-1,1]

theorem originalTriangularInverseProducts :
    originalTriangularS1*originalTriangularS1i=1 ∧ originalTriangularS1i*originalTriangularS1=1 ∧
    originalTriangularS2*originalTriangularS2i=1 ∧ originalTriangularS2i*originalTriangularS2=1 := by
  repeat' constructor
  all_goals ext i j; fin_cases i <;> fin_cases j <;> norm_num [originalTriangularS1,originalTriangularS1i,originalTriangularS2,originalTriangularS2i,Matrix.mul_apply,Fin.sum_univ_succ]

theorem originalTriangularCharpoly :
    originalTriangularMatrix.charpoly=(X-C (2:ℚ))^3 := by
  norm_num [Matrix.charpoly,Matrix.charmatrix,Matrix.det_fin_three,originalTriangularMatrix,Polynomial.C_ofNat]
  <;> ring

theorem originalFirstTriangularStep :
    originalTriangularS1 * originalTriangularMatrix * originalTriangularS1i =
      !![2,4,3;0,4,2;0,-2,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [originalTriangularS1,originalTriangularMatrix,originalTriangularS1i,Matrix.mul_apply,Fin.sum_univ_succ]

theorem originalSecondTriangularStep :
    originalTriangularS2 * originalTriangularS1 * originalTriangularMatrix *
      originalTriangularS1i * originalTriangularS2i = !![2,1,3;0,2,2;0,0,2] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [originalTriangularS1,originalTriangularMatrix,originalTriangularS1i,originalTriangularS2,originalTriangularS2i,Matrix.mul_apply,Fin.sum_univ_succ]

end ILab.LinearAlgebra
