import ILab.LinearAlgebra.VolumesDeterminants
import ILab.LinearAlgebra.MatrixEquivalence
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Holstein §7.3. Fin indices start at0; deleting uses succAbove in the
original remaining order. Adding2 to i+j does not change the sign.
Existence uses Mathlib's determinant and the previously checked axioms;
this file does NOT claim to reproduce Holstein's inductive construction.
Laplace identities are checked separately over arbitrary fields, including
characteristic2. No verification of the JavaScript implementation is claimed. -/
namespace ILab.LinearAlgebra
open Matrix Module

theorem determinantExistsUnique {K : Type*} [Field K] (n : ℕ) :
    ∃! d : Matrix (Fin n) (Fin n) K → K, satisfiesRowDeterminantAxioms n d := by
  refine ⟨Matrix.det, canonicalDeterminantAxioms n, ?_⟩
  intro d hd
  exact rowDeterminantEqualsCanonical d hd

def deletionMinor {K : Type*} {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (i j : Fin (n+1)) : Matrix (Fin n) (Fin n) K := A.submatrix i.succAbove j.succAbove

theorem deletionMinorEntry {K : Type*} {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (i j : Fin (n+1)) (r c : Fin n) :
    deletionMinor A i j r c = A (i.succAbove r) (j.succAbove c) := rfl

theorem laplaceColumn {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (j : Fin (n+1)) :
    A.det = ∑ i : Fin (n+1), (-1 : K)^(i.val+j.val)*A i j*(deletionMinor A i j).det :=
  Matrix.det_succ_column A j

theorem laplaceColumnsAgree {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (j k : Fin (n+1)) :
    (∑ i : Fin (n+1), (-1 : K)^(i.val+j.val)*A i j*(deletionMinor A i j).det) =
    ∑ i : Fin (n+1), (-1 : K)^(i.val+k.val)*A i k*(deletionMinor A i k).det := by
  rw [← laplaceColumn A j, ← laplaceColumn A k]

theorem cofactorPrintedSign {K : Type*} [Field K] (i j : ℕ) :
    (-1 : K)^((i+1)+(j+1)) = (-1 : K)^(i+j) := by
  have h : (i+1)+(j+1) = (i+j)+2 := by omega
  rw [h, pow_add]; norm_num

theorem laplaceThreeTerms {K : Type*} [Field K] (A : Matrix (Fin 3) (Fin 3) K) :
    A.det = A 0 0*A 1 1*A 2 2-A 0 0*A 1 2*A 2 1-
      A 1 0*A 0 1*A 2 2+A 1 0*A 2 1*A 0 2+
      A 2 0*A 0 1*A 1 2-A 2 0*A 0 2*A 1 1 := by
  rw [det_fin_three]; ring

theorem complexColumnExpansion :
    (0 : ℂ)*(Complex.I*4-3)-1*(4-3*Complex.I)+2*(1-Complex.I^2) = 3*Complex.I := by
  norm_num [Complex.I_sq]

theorem sarrusFourCounterexample :
    Matrix.det (!![0,1,0,0;1,0,0,0;0,0,1,0;0,0,0,1] : Matrix (Fin 4) (Fin 4) ℚ) = -1 := by
  rw [Matrix.det_succ_row _ 0]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]

theorem determinantColumnAdd {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (j : Fin n) (u v : Fin n → K) :
    (A.updateCol j (u+v)).det = (A.updateCol j u).det+(A.updateCol j v).det :=
  Matrix.det_updateCol_add A j u v

theorem determinantColumnScale {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (j : Fin n) (s : K) (u : Fin n → K) :
    (A.updateCol j (s • u)).det = s*(A.updateCol j u).det :=
  Matrix.det_updateCol_smul A j s u

theorem determinantUnitIffNonzero {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem determinantFullRankIff {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : A.rank = n ↔ A.det ≠ 0 := by
  constructor
  · intro h
    apply (determinantUnitIffNonzero A).mp
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    change Function.Surjective A.mulVecLin
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h
  · intro h
    simpa using Matrix.rank_of_det_ne_zero h

theorem determinantZeroIffRankDefect {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : A.det = 0 ↔ A.rank < n := by
  have hb : A.rank ≤ n := by simpa using A.rank_le_card_width
  have h := determinantFullRankIff A
  constructor
  · intro hz
    have hn : A.rank ≠ n := by intro he; exact (h.mp he) hz
    omega
  · intro hl
    by_contra hn
    have := h.mpr hn
    omega

theorem determinantZeroIffNontrivialKernel {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : A.det = 0 ↔ ∃ v ≠ 0, A *ᵥ v = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.symm

theorem determinantFourCriteria {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    (IsUnit A ↔ A.rank = n) ∧ (A.rank = n ↔ A.transpose.rank = n) ∧
      (A.transpose.rank = n ↔ A.det ≠ 0) := by
  rw [Matrix.rank_transpose]
  exact ⟨(determinantUnitIffNonzero A).trans (determinantFullRankIff A).symm,
    Iff.rfl, determinantFullRankIff A⟩

theorem determinantTranspose {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : A.transpose.det = A.det := Matrix.det_transpose A

theorem laplaceRow {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (i : Fin (n+1)) :
    A.det = ∑ j : Fin (n+1), (-1 : K)^(i.val+j.val)*A i j*(deletionMinor A i j).det :=
  Matrix.det_succ_row A i

theorem laplaceRowColumnAgree {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (i j : Fin (n+1)) :
    (∑ k : Fin (n+1), (-1 : K)^(i.val+k.val)*A i k*(deletionMinor A i k).det) =
    ∑ k : Fin (n+1), (-1 : K)^(k.val+j.val)*A k j*(deletionMinor A k j).det := by
  rw [← laplaceRow A i, ← laplaceColumn A j]

theorem determinantColumnSwap {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (h : i ≠ j) :
    (A.submatrix id (Equiv.swap i j)).det = -A.det := by
  rw [Matrix.det_permute']
  simp [Equiv.Perm.sign_swap h]

theorem complexRowExpansion :
    (-2 : ℂ)+Complex.I*(3-2*Complex.I) = 3*Complex.I := by
  calc
    (-2 : ℂ)+Complex.I*(3-2*Complex.I) = 3*Complex.I-2*(Complex.I^2+1) := by ring
    _ = 3*Complex.I := by rw [Complex.I_sq]; ring

end ILab.LinearAlgebra
