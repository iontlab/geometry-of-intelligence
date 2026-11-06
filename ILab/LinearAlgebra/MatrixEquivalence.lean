import ILab.LinearAlgebra.CoordinateChanges
import ILab.LinearAlgebra.ElementaryMatrices
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Holstein §5.5, LA-P020, printed92–96. Matrix equivalence uses independent
units; similarity uses the same unit on both sides. Matrix.rank is the finite
dimension of the image of mulVecLin; columnRank and rowRank below explicitly
use spans, not different unconnected numerical rank definitions.
The source's false relation in5.5.7 is preserved in Mathematics and refuted
below; only the separately labelled corrected relation is proved to be zero.
The square rank-normal-form theorem is explicitly marked as a square special
case of5.5.4; the general rectangular source theorem remains in Mathematics.
No claim of formal verification of JavaScript elimination. -/
noncomputable section
namespace ILab.LinearAlgebra
open Matrix Module
variable {K : Type*} [Field K] {m n : ℕ}

def matrixEquivalent (X Y : Matrix (Fin m) (Fin n) K) : Prop :=
  ∃ (S : (Matrix (Fin m) (Fin m) K)ˣ) (T : (Matrix (Fin n) (Fin n) K)ˣ),
    Y = (S.val) * X * (↑T⁻¹ : Matrix _ _ K)

def matrixSimilar (X Y : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ T : (Matrix (Fin n) (Fin n) K)ˣ,
    Y = (T.val) * X * (↑T⁻¹ : Matrix _ _ K)

theorem similarityImpliesEquivalence {X Y : Matrix (Fin n) (Fin n) K}
    (h : matrixSimilar X Y) : matrixEquivalent X Y := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, T, hT⟩

theorem matrixEquivalentRefl (X : Matrix (Fin m) (Fin n) K) : matrixEquivalent X X := by
  exact ⟨1, 1, by simp⟩

theorem matrixEquivalentSymm {X Y : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) : matrixEquivalent Y X := by
  obtain ⟨S, T, rfl⟩ := h
  refine ⟨S⁻¹, T⁻¹, ?_⟩
  simp [← Matrix.mul_assoc]

theorem matrixEquivalentTrans {X Y Z : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) (h' : matrixEquivalent Y Z) : matrixEquivalent X Z := by
  obtain ⟨S, T, rfl⟩ := h
  obtain ⟨U, V, rfl⟩ := h'
  refine ⟨U * S, V * T, ?_⟩
  simp [Matrix.mul_assoc]

theorem matrixEquivalentEquivalence : Equivalence (@matrixEquivalent K _ m n) :=
  ⟨matrixEquivalentRefl, fun h => matrixEquivalentSymm h, fun h h' => matrixEquivalentTrans h h'⟩

theorem matrixSimilarRefl (X : Matrix (Fin n) (Fin n) K) : matrixSimilar X X := by
  exact ⟨1, by simp⟩

theorem matrixSimilarSymm {X Y : Matrix (Fin n) (Fin n) K}
    (h : matrixSimilar X Y) : matrixSimilar Y X := by
  obtain ⟨T, rfl⟩ := h
  exact ⟨T⁻¹, by simp [← Matrix.mul_assoc]⟩

theorem matrixSimilarTrans {X Y Z : Matrix (Fin n) (Fin n) K}
    (h : matrixSimilar X Y) (h' : matrixSimilar Y Z) : matrixSimilar X Z := by
  obtain ⟨T, rfl⟩ := h
  obtain ⟨V, rfl⟩ := h'
  exact ⟨V*T, by simp [Matrix.mul_assoc]⟩

theorem matrixSimilarEquivalence : Equivalence (@matrixSimilar K _ n) :=
  ⟨matrixSimilarRefl, fun h => matrixSimilarSymm h, fun h h' => matrixSimilarTrans h h'⟩

theorem identityEquivalentUnit (S : (Matrix (Fin n) (Fin n) K)ˣ) :
    matrixEquivalent 1 (S.val) := ⟨S, 1, by simp⟩

theorem identitySimilarOnlyIdentity (Y : Matrix (Fin n) (Fin n) K) :
    matrixSimilar 1 Y ↔ Y = 1 := by
  constructor
  · rintro ⟨T, rfl⟩
    simp
  · rintro rfl
    exact matrixSimilarRefl _

theorem rankInvariantLeft (X : Matrix (Fin m) (Fin n) K)
    (S : (Matrix (Fin m) (Fin m) K)ˣ) : ((S.val)*X).rank = X.rank :=
  Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_iff_isUnit_det _ |>.mp S.isUnit)

theorem rankInvariantRight (X : Matrix (Fin m) (Fin n) K)
    (T : (Matrix (Fin n) (Fin n) K)ˣ) : (X*(T.val)).rank = X.rank :=
  Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_iff_isUnit_det _ |>.mp T.isUnit)

theorem equivalentMatricesSameRank {X Y : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) : X.rank = Y.rank := by
  obtain ⟨S,T,rfl⟩ := h
  rw [rankInvariantRight, rankInvariantLeft]

def columnRank (X : Matrix (Fin m) (Fin n) K) : ℕ :=
  finrank K (Submodule.span K (Set.range X.col))

def rowRank (X : Matrix (Fin m) (Fin n) K) : ℕ :=
  finrank K (Submodule.span K (Set.range X.row))

theorem columnRankEqualsMatrixRank (X : Matrix (Fin m) (Fin n) K) :
    columnRank X = X.rank := (Matrix.rank_eq_finrank_span_cols X).symm

theorem rowRankEqualsMatrixRank (X : Matrix (Fin m) (Fin n) K) :
    rowRank X = X.rank := (Matrix.rank_eq_finrank_span_row X).symm

theorem columnRankEqualsMapRank (X : Matrix (Fin m) (Fin n) K) :
    columnRank X = finrank K (LinearMap.range X.mulVecLin) := columnRankEqualsMatrixRank X

theorem rankOfAnyRepresentingMatrix {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (f : V →ₗ[K] W) : columnRank (matrixRepresentation a b f) = finrank K (LinearMap.range f) := by
  rw [columnRankEqualsMatrixRank, matrixRepresentation,
    Matrix.rank_eq_finrank_range_toLin _ b a, Matrix.toLin_toMatrix]

theorem equivalentMatricesSameColumnRank {X Y : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) : columnRank X = columnRank Y := by
  simpa [columnRankEqualsMatrixRank] using equivalentMatricesSameRank h

theorem inverseTranspose (S : (Matrix (Fin n) (Fin n) K)ˣ) :
    (↑S⁻¹ : Matrix _ _ K)ᵀ = (S.val)ᵀ⁻¹ := by
  rw [← Matrix.transpose_nonsing_inv]
  congr 1
  exact (Matrix.inv_eq_left_inv (S.inv_val)).symm

theorem transposeSwapsRanks (X : Matrix (Fin m) (Fin n) K) :
    columnRank X = rowRank Xᵀ ∧ rowRank X = columnRank Xᵀ := by
  simp [columnRankEqualsMatrixRank, rowRankEqualsMatrixRank, Matrix.rank_transpose]

theorem equivalentMatricesSameRowRank {X Y : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) : rowRank X = rowRank Y := by
  simpa [rowRankEqualsMatrixRank] using equivalentMatricesSameRank h

theorem rowRankEqualsColumnRank (X : Matrix (Fin m) (Fin n) K) :
    rowRank X = columnRank X := by
  rw [rowRankEqualsMatrixRank, columnRankEqualsMatrixRank]

theorem squareRankNormalForm (X : Matrix (Fin n) (Fin n) K) :
    ∃ (L R : Matrix (Fin n) (Fin n) K)
      (e : Fin n ≃ Fin X.rank ⊕ Fin (Fintype.card (Fin n)-X.rank)),
      IsUnit L ∧ IsUnit R ∧ L*X*R =
        (Matrix.fromBlocks (1 : Matrix (Fin X.rank) (Fin X.rank) K) 0 0
          (0 : Matrix (Fin (Fintype.card (Fin n)-X.rank)) (Fin (Fintype.card (Fin n)-X.rank)) K)).submatrix e e := by
  exact Matrix.exists_rank_normal_form X

theorem equivalenceViaCommonForm (X Y N : Matrix (Fin m) (Fin n) K)
    (L₁ L₂ : (Matrix (Fin m) (Fin m) K)ˣ)
    (R₁ R₂ : (Matrix (Fin n) (Fin n) K)ˣ)
    (hx : (L₁.val)*X*(R₁.val)=N)
    (hy : (L₂.val)*Y*(R₂.val)=N) : matrixEquivalent X Y := by
  apply matrixEquivalentTrans (Y := N)
  · exact ⟨L₁,R₁⁻¹, by simpa using hx.symm⟩
  · apply matrixEquivalentSymm
    exact ⟨L₂,R₂⁻¹, by simpa using hy.symm⟩

theorem unitInverseAsMatrixInverse (T : (Matrix (Fin n) (Fin n) K)ˣ) :
    (↑T⁻¹ : Matrix _ _ K) = (T.val)⁻¹ := by
  exact (Matrix.inv_eq_left_inv (T.inv_val)).symm

def coordinateChangeAsUnit {V : Type*} [AddCommGroup V] [Module K V]
    (a a' : Basis (Fin n) K V) : (Matrix (Fin n) (Fin n) K)ˣ :=
  (coordinateChangeIsUnit a a').unit

theorem coordinateChangeAsUnitValue {V : Type*} [AddCommGroup V] [Module K V]
    (a a' : Basis (Fin n) K V) :
    (coordinateChangeAsUnit a a' : Matrix _ _ K) = coordinateChange a a' :=
  (coordinateChangeIsUnit a a').unit_spec

theorem sameMapGivesEquivalentMatrices {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (a a' : Basis (Fin n) K V)
    (b b' : Basis (Fin m) K W) (f : V →ₗ[K] W) :
    matrixEquivalent (matrixRepresentation a b f) (matrixRepresentation a' b' f) := by
  refine ⟨coordinateChangeAsUnit b b',coordinateChangeAsUnit a a', ?_⟩
  rw [unitInverseAsMatrixInverse, coordinateChangeAsUnitValue, coordinateChangeAsUnitValue]
  exact matrixChangeFormula a a' b b' f

theorem sameEndomorphismGivesSimilarMatrices {V : Type*} [AddCommGroup V] [Module K V]
    (a a' : Basis (Fin n) K V) (f : V →ₗ[K] V) :
    matrixSimilar (matrixRepresentation a a f) (matrixRepresentation a' a' f) := by
  refine ⟨coordinateChangeAsUnit a a', ?_⟩
  rw [unitInverseAsMatrixInverse, coordinateChangeAsUnitValue]
  exact endomorphismChangeFormula a a' f

/-- This basis has coordinate reader T, hence synthesis T inverse. -/
def basisWithReader (T : (Matrix (Fin n) (Fin n) K)ˣ) : Basis (Fin n) K (Fin n → K) :=
  Basis.ofEquivFun (Matrix.toLinearEquiv (Pi.basisFun K (Fin n)) (T.val)
    ((Matrix.isUnit_iff_isUnit_det _).mp T.isUnit))

theorem basisWithReaderCoordinates (T : (Matrix (Fin n) (Fin n) K)ˣ) (v : Fin n → K) :
    (basisWithReader T).repr v = (T.val) *ᵥ v := by
  ext i
  simp [basisWithReader, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem readerIsCoordinateChange (T : (Matrix (Fin n) (Fin n) K)ˣ) :
    coordinateChange (Pi.basisFun K (Fin n)) (basisWithReader T) = (T.val) := by
  ext i j
  simp [coordinateChangeEntry, basisWithReaderCoordinates, Pi.basisFun_apply]

theorem standardMatrixRecovery (X : Matrix (Fin m) (Fin n) K) :
    matrixRepresentation (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin m))
      (Matrix.toLin' X) = X := by
  ext i j
  simp [matrixRepresentationEntry, Pi.basisFun_apply, Matrix.toLin'_apply]

theorem equivalentMatricesHaveCommonCoordinateMap {X Y : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) :
    ∃ (a' : Basis (Fin n) K (Fin n → K)) (b' : Basis (Fin m) K (Fin m → K))
      (f : (Fin n → K) →ₗ[K] (Fin m → K)),
      matrixRepresentation (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin m)) f = X ∧
      matrixRepresentation a' b' f = Y := by
  obtain ⟨S,T,rfl⟩ := h
  let f := Matrix.toLin' X
  refine ⟨basisWithReader T, basisWithReader S, f, ?_, ?_⟩
  · simpa only [f, standardMatrixRecovery]
  · rw [matrixChangeFormula (Pi.basisFun K (Fin n)) (basisWithReader T)
        (Pi.basisFun K (Fin m)) (basisWithReader S), readerIsCoordinateChange,
        readerIsCoordinateChange, ← unitInverseAsMatrixInverse]
    simpa only [f, standardMatrixRecovery]

theorem similarMatricesHaveCommonEndomorphism {X Y : Matrix (Fin n) (Fin n) K}
    (h : matrixSimilar X Y) :
    ∃ (a' : Basis (Fin n) K (Fin n → K)) (f : (Fin n → K) →ₗ[K] (Fin n → K)),
      matrixRepresentation (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) f = X ∧
      matrixRepresentation a' a' f = Y := by
  obtain ⟨T,rfl⟩ := h
  let f := Matrix.toLin' X
  refine ⟨basisWithReader T,f, ?_, ?_⟩
  · simpa only [f, standardMatrixRecovery]
  · rw [endomorphismChangeFormula (Pi.basisFun K (Fin n)) (basisWithReader T),
      readerIsCoordinateChange, ← unitInverseAsMatrixInverse]
    simpa only [f, standardMatrixRecovery]

def transposedUnit (T : (Matrix (Fin n) (Fin n) K)ˣ) :
    (Matrix (Fin n) (Fin n) K)ˣ where
  val := T.valᵀ
  inv := (↑T⁻¹ : Matrix _ _ K)ᵀ
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp

theorem transposePreservesEquivalence {X Y : Matrix (Fin m) (Fin n) K}
    (h : matrixEquivalent X Y) : matrixEquivalent Xᵀ Yᵀ := by
  obtain ⟨S,T,rfl⟩ := h
  refine ⟨transposedUnit T⁻¹,transposedUnit S⁻¹, ?_⟩
  simp [transposedUnit, Matrix.transpose_mul, Matrix.mul_assoc]

theorem columnOperationIsTransposedRowOperation (X : Matrix (Fin m) (Fin n) K)
    (D : Matrix (Fin n) (Fin n) K) : X*Dᵀ = (D*Xᵀ)ᵀ := by
  simp [Matrix.transpose_mul]

theorem columnAdditionAction (X : Matrix (Fin m) (Fin n) K)
    (source target : Fin n) (c : K) :
    ∀ i, (X*(Matrix.transvection target source c)ᵀ) i target =
      X i target + c*X i source := by
  intro i
  rw [columnOperationIsTransposedRowOperation]
  exact addElementaryAction Xᵀ source target c i

theorem invertibleColumnOperationPreservesRank (X : Matrix (Fin m) (Fin n) K)
    (D : (Matrix (Fin n) (Fin n) K)ˣ) : (X*(transposedUnit D).val).rank = X.rank :=
  rankInvariantRight X (transposedUnit D)

theorem independentColumnsAttainColumnRank (X : Matrix (Fin m) (Fin n) K) :
    ∃ t : Finset (Fin m → K), (↑t : Set (Fin m → K)) ⊆ Set.range X.col ∧
      t.card = columnRank X ∧ Submodule.span K (↑t : Set (Fin m → K)) =
      Submodule.span K (Set.range X.col) ∧ LinearIndepOn K id (↑t : Set (Fin m → K)) := by
  exact Submodule.exists_finset_span_eq_linearIndepOn K (Set.range X.col)

theorem independentColumnsBound (X : Matrix (Fin m) (Fin n) K)
    (t : Finset (Fin m → K)) (ht : (↑t : Set (Fin m → K)) ⊆ Set.range X.col)
    (hi : LinearIndepOn K id (↑t : Set (Fin m → K))) : t.card ≤ columnRank X := by
  rw [← finrank_span_finset_eq_card hi]
  exact Submodule.finrank_mono (Submodule.span_mono ht)

theorem independentRowsAttainRowRank (X : Matrix (Fin m) (Fin n) K) :
    ∃ t : Finset (Fin n → K), (↑t : Set (Fin n → K)) ⊆ Set.range X.row ∧
      t.card = rowRank X ∧ Submodule.span K (↑t : Set (Fin n → K)) =
      Submodule.span K (Set.range X.row) ∧ LinearIndepOn K id (↑t : Set (Fin n → K)) := by
  exact Submodule.exists_finset_span_eq_linearIndepOn K (Set.range X.row)

theorem independentRowsBound (X : Matrix (Fin m) (Fin n) K)
    (t : Finset (Fin n → K)) (ht : (↑t : Set (Fin n → K)) ⊆ Set.range X.row)
    (hi : LinearIndepOn K id (↑t : Set (Fin n → K))) : t.card ≤ rowRank X := by
  rw [← finrank_span_finset_eq_card hi]
  exact Submodule.finrank_mono (Submodule.span_mono ht)

theorem originalPrintedRelationIsFalse :
    (10 : ℚ) • (![1,2] : Fin 2 → ℚ) - (3 : ℚ) • (![2,0] : Fin 2 → ℚ) + (4 : ℚ) • (![-1,5] : Fin 2 → ℚ) = ![0,40] := by
  ext i
  fin_cases i <;> norm_num

theorem originalCorrectedRelation :
    (10 : ℚ) • (![1,2] : Fin 2 → ℚ) - (7 : ℚ) • (![2,0] : Fin 2 → ℚ) - (4 : ℚ) • (![-1,5] : Fin 2 → ℚ) = 0 := by
  ext i
  fin_cases i <;> norm_num

end ILab.LinearAlgebra
