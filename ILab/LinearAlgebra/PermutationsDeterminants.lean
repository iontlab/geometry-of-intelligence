import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.ZMod.Basic

/-! Holstein §7.5. Convention is proved explicitly: Eσ[i,j]=δ(i,σ(j)).
Mathlib's direct permMatrix has the opposite orientation, so its homomorphism
uses σ⁻¹. Integer-unit sign and its field interpretation are separate.
The row-oriented Leibniz identity below uses Mathlib's determinant definition
and transpose theorem, not a claim of a new formal copy of Holstein's entire
multilinearity proof. No JavaScript or complexity verification is claimed. -/
noncomputable section
namespace ILab.LinearAlgebra
open Matrix Equiv
variable {n : ℕ} {K : Type*} [Field K]

theorem transpositionInverse (i j : Fin n) : (Equiv.swap i j)⁻¹ = Equiv.swap i j :=
  Equiv.swap_inv i j

theorem transpositionSquare (i j : Fin n) : Equiv.swap i j * Equiv.swap i j = 1 := by
  simp

theorem permutationTranspositionProduct (σ : Equiv.Perm (Fin n)) :
    ∃ l : List (Equiv.Perm (Fin n)), l.prod = σ ∧ ∀ t ∈ l, t.IsSwap := by
  exact ⟨σ.swapFactors.val, σ.swapFactors.property⟩

def holsteinPermutationMatrix : Equiv.Perm (Fin n) →* Matrix (Fin n) (Fin n) K :=
  Matrix.permMatrixHom

theorem holsteinPermutationEntry (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    holsteinPermutationMatrix (K := K) σ i j = if i = σ j then 1 else 0 := by
  change (σ⁻¹.permMatrix K) i j = _
  have h : (j = σ.symm i) ↔ (i = σ j) := by
    constructor <;> intro h
    · rw [h]; simp
    · rw [h]; simp
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff, Equiv.Perm.inv_def]
  by_cases hs : σ.symm i = j
  · have hi : i = σ j := h.mp hs.symm
    simp [hi]
  · have hi : i ≠ σ j := fun hi => hs (h.mpr hi).symm
    simp [hs, hi]

theorem holsteinPermutationProduct (σ τ : Equiv.Perm (Fin n)) :
    (holsteinPermutationMatrix (K := K) σ) * holsteinPermutationMatrix τ =
      holsteinPermutationMatrix (σ * τ) := by
  exact (map_mul holsteinPermutationMatrix σ τ).symm

theorem holsteinPermutationIdentity :
    holsteinPermutationMatrix (K := K) (1 : Equiv.Perm (Fin n)) = 1 :=
  map_one holsteinPermutationMatrix

theorem holsteinPermutationInverse (σ : Equiv.Perm (Fin n)) :
    holsteinPermutationMatrix (K := K) σ * holsteinPermutationMatrix σ⁻¹ = 1 := by
  rw [holsteinPermutationProduct, mul_inv_cancel, holsteinPermutationIdentity]

theorem holsteinPermutationDet (σ : Equiv.Perm (Fin n)) :
    (holsteinPermutationMatrix (K := K) σ).det = (Equiv.Perm.sign σ : K) := by
  change (σ⁻¹.permMatrix K).det = _
  rw [Matrix.det_permutation, Equiv.Perm.sign_inv]

def integerPermutationSign : Equiv.Perm (Fin n) →* ℤˣ := Equiv.Perm.sign

theorem permutationSignProduct (σ τ : Equiv.Perm (Fin n)) :
    integerPermutationSign (σ * τ) = integerPermutationSign σ * integerPermutationSign τ :=
  map_mul integerPermutationSign σ τ

theorem permutationSignInverse (σ : Equiv.Perm (Fin n)) :
    integerPermutationSign σ⁻¹ = integerPermutationSign σ := Equiv.Perm.sign_inv σ

theorem transpositionSign (i j : Fin n) (h : i ≠ j) :
    integerPermutationSign (Equiv.swap i j) = -1 := Equiv.Perm.sign_swap h

theorem permutationFactorParity (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ t ∈ l, t.IsSwap) : integerPermutationSign l.prod = (-1 : ℤˣ)^l.length :=
  Equiv.Perm.sign_prod_list_swap hl

theorem permutationParityIndependent (l m : List (Equiv.Perm (Fin n)))
    (hl : ∀ t ∈ l, t.IsSwap) (hm : ∀ t ∈ m, t.IsSwap) (h : l.prod = m.prod) :
    (-1 : ℤˣ)^l.length = (-1 : ℤˣ)^m.length := by
  rw [← permutationFactorParity l hl, ← permutationFactorParity m hm, h]

theorem signCollapseCharacteristicTwo : (-1 : ZMod 2) = 1 := by decide

def holsteinAlternatingGroup (n : ℕ) : Subgroup (Equiv.Perm (Fin n)) :=
  (integerPermutationSign (n := n)).ker

theorem holsteinAlternatingMembership (σ : Equiv.Perm (Fin n)) :
    σ ∈ holsteinAlternatingGroup n ↔ integerPermutationSign σ = 1 := Iff.rfl

theorem holsteinAlternatingEqualsMathlib : holsteinAlternatingGroup n = alternatingGroup (Fin n) :=
  rfl

theorem holsteinAlternatingCard [Nontrivial (Fin n)] :
    Nat.card (holsteinAlternatingGroup n) = n.factorial / 2 := by
  change Nat.card (alternatingGroup (Fin n)) = _
  simpa using (nat_card_alternatingGroup (α := Fin n))

theorem holsteinAlternatingOne : Nat.card (holsteinAlternatingGroup 1) = 1 := by
  change Nat.card (alternatingGroup (Fin 1)) = 1
  exact Nat.card_unique

theorem permutationSignByInversionFactors (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = ∏ i, ∏ j > i, if σ i < σ j then 1 else -1 :=
  σ.sign_eq_prod_prod_Ioi

theorem rowLeibnizFormula (A : Matrix (Fin n) (Fin n) K) :
    A.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : K) * ∏ i, A i (σ i) := by
  calc A.det = A.transpose.det := (Matrix.det_transpose A).symm
       _ = _ := by simpa only [Matrix.transpose_apply] using Matrix.det_apply' A.transpose

theorem leibnizTwo (A : Matrix (Fin 2) (Fin 2) K) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A

theorem leibnizThree (A : Matrix (Fin 3) (Fin 3) K) :
    A.det = A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
      A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
      A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := Matrix.det_fin_three A

theorem blockTriangularDet {m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin n) (Fin m) K) (B : Matrix (Fin m) (Fin m) K) :
    (Matrix.fromBlocks A C 0 B).det = A.det * B.det :=
  Matrix.det_fromBlocks_zero₂₁ A C B

theorem blockPermutationSign {m : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (Equiv.Perm.sumCongr σ τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ :=
  Equiv.Perm.sign_sumCongr σ τ

end ILab.LinearAlgebra
