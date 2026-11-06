import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.Tactic

/-! Holstein §§7.1–7.2. Coordinates use Fin indices 0,1,2 for printed 1,2,3.
The Euclidean norm is the L2 norm of WithLp.toLp 2 v, never the Pi sup norm.
Algebraic determinant axioms are formalized in arbitrary finite dimension;
the library's canonical determinant is used for verification, without claiming
to reproduce the subsequent original §7.3 existence proof or geometric measure. -/
namespace ILab.LinearAlgebra
open Matrix Module
open scoped BigOperators Matrix

def basisParallelotope {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {p | ∃ a : Fin n → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧ p = ∑ i, a i • b i}

theorem parallelotopeContainsOrigin {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    (0 : Fin n → ℝ) ∈ basisParallelotope b := by
  refine ⟨0, ?_, ?_⟩ <;> simp

theorem euclideanInnerCoordinates {n : ℕ} (v w : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 w) = v ⬝ᵥ w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem coordinateDotSymmetric {n : ℕ} (v w : Fin n → ℝ) : v ⬝ᵥ w = w ⬝ᵥ v :=
  dotProduct_comm v w

theorem coordinateDotBilinear {n : ℕ} (u v w : Fin n → ℝ) (a b : ℝ) :
    (a • v + b • w) ⬝ᵥ u = a * (v ⬝ᵥ u) + b * (w ⬝ᵥ u) := by
  simp [dotProduct, Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]

theorem euclideanNormCoordinates {n : ℕ} (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 v‖ = Real.sqrt (v ⬝ᵥ v) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [dotProduct, Real.norm_eq_abs, sq_abs, pow_two]

theorem coordinateNormNonnegative {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ Real.sqrt (v ⬝ᵥ v) := Real.sqrt_nonneg _

theorem coordinateNormZeroIff {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (v ⬝ᵥ v) = 0 ↔ v = 0 := by
  rw [← euclideanNormCoordinates, norm_eq_zero]
  constructor
  · intro h; simpa using congrArg WithLp.ofLp h
  · intro h; subst v; rfl

theorem crossCoordinates (v w : Fin 3 → ℝ) :
    v ⨯₃ w = ![v 1*w 2-v 2*w 1, v 2*w 0-v 0*w 2, v 0*w 1-v 1*w 0] :=
  cross_apply v w

theorem crossAntisymmetric (v w : Fin 3 → ℝ) : v ⨯₃ w = -(w ⨯₃ v) := by
  simpa using (cross_anticomm w v).symm

theorem crossSameZero (v : Fin 3 → ℝ) : v ⨯₃ v = 0 := cross_self v

theorem crossBilinear (u v w : Fin 3 → ℝ) (a b : ℝ) :
    (a • v + b • w) ⨯₃ u = a • (v ⨯₃ u) + b • (w ⨯₃ u) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

theorem crossOrthogonalBoth (v w : Fin 3 → ℝ) :
    v ⬝ᵥ (v ⨯₃ w) = 0 ∧ w ⬝ᵥ (v ⨯₃ w) = 0 :=
  ⟨dot_self_cross v w, dot_cross_self v w⟩

theorem crossStandardBasis :
    (![1,0,0] : Fin 3 → ℝ) ⨯₃ ![0,1,0] = ![0,0,1] ∧
    (![1,0,0] : Fin 3 → ℝ) ⨯₃ ![0,0,1] = ![0,-1,0] ∧
    (![0,1,0] : Fin 3 → ℝ) ⨯₃ ![0,0,1] = ![1,0,0] := by
  norm_num [cross_apply]

theorem crossNormAngle (v w : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (v ⨯₃ w)‖ = ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖ *
      Real.sin (InnerProductGeometry.angle (WithLp.toLp 2 v) (WithLp.toLp 2 w)) :=
  InnerProductGeometry.norm_toLp_symm_crossProduct v w

theorem scalarTripleCyclic (u v w : Fin 3 → ℝ) :
    (u ⨯₃ v) ⬝ᵥ w = u ⬝ᵥ (v ⨯₃ w) := by
  rw [dotProduct_comm]
  exact triple_product_permutation w u v

theorem epsilonCyclic (i j k : Fin 3) :
    ((Pi.single i (1 : ℝ)) ⨯₃ (Pi.single j 1)) ⬝ᵥ (Pi.single k 1) =
    ((Pi.single k (1 : ℝ)) ⨯₃ (Pi.single i 1)) ⬝ᵥ (Pi.single j 1) := by
  rw [scalarTripleCyclic, dotProduct_comm, scalarTripleCyclic, dotProduct_comm]

def scalarTriple (a b c : Fin 3 → ℝ) : ℝ := a ⬝ᵥ (b ⨯₃ c)

theorem scalarTripleLinearEach (a b c d : Fin 3 → ℝ) (s t : ℝ) :
    scalarTriple (s • a + t • d) b c = s * scalarTriple a b c + t * scalarTriple d b c ∧
    scalarTriple a (s • b + t • d) c = s * scalarTriple a b c + t * scalarTriple a d c ∧
    scalarTriple a b (s • c + t • d) = s * scalarTriple a b c + t * scalarTriple a b d := by
  constructor
  · simp [scalarTriple, cross_apply, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · constructor <;> simp [scalarTriple, cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

theorem scalarTripleAlternating (a b : Fin 3 → ℝ) :
    scalarTriple a b b = 0 ∧ scalarTriple a a b = 0 ∧ scalarTriple a b a = 0 := by
  simp [scalarTriple]

theorem scalarTripleNormalized :
    scalarTriple (![1,0,0] : Fin 3 → ℝ) ![0,1,0] ![0,0,1] = 1 := by
  norm_num [scalarTriple, cross_apply, vec3_dotProduct]

theorem scalarTripleRows (a b c : Fin 3 → ℝ) :
    scalarTriple a b c = Matrix.det ![a,b,c] := triple_product_eq_det a b c

theorem scalarTripleSignedHeight (a b c : Fin 3 → ℝ)
    (h : Real.sqrt ((b ⨯₃ c) ⬝ᵥ (b ⨯₃ c)) ≠ 0) :
    Real.sqrt ((b ⨯₃ c) ⬝ᵥ (b ⨯₃ c)) *
      (scalarTriple a b c / Real.sqrt ((b ⨯₃ c) ⬝ᵥ (b ⨯₃ c))) = scalarTriple a b c := by
  field_simp

theorem scalarTripleAreaHeight (a b c : Fin 3 → ℝ)
    (h : Real.sqrt ((b ⨯₃ c) ⬝ᵥ (b ⨯₃ c)) ≠ 0) :
    Real.sqrt ((b ⨯₃ c) ⬝ᵥ (b ⨯₃ c)) *
      (|scalarTriple a b c| / Real.sqrt ((b ⨯₃ c) ⬝ᵥ (b ⨯₃ c))) = |scalarTriple a b c| := by
  field_simp

def satisfiesRowDeterminantAxioms {K : Type*} [Field K] (n : ℕ)
    (d : Matrix (Fin n) (Fin n) K → K) : Prop :=
  (∀ (A : Matrix (Fin n) (Fin n) K) i u v, d (A.updateRow i (u+v)) = d (A.updateRow i u) + d (A.updateRow i v)) ∧
  (∀ (A : Matrix (Fin n) (Fin n) K) i (s : K) u, d (A.updateRow i (s • u)) = s * d (A.updateRow i u)) ∧
  (∀ A i j, i ≠ j → A i = A j → d A = 0) ∧ d 1 = 1

def rowDeterminantAlternating {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d) :
    (Fin n → K) [⋀^Fin n]→ₗ[K] K := by
  let eqFin : DecidableEq (Fin n) := inferInstance
  refine { toFun := d, map_update_add' := ?_, map_update_smul' := ?_, map_eq_zero_of_eq' := ?_ }
  · intro inst A i u v
    have heq : inst = eqFin := Subsingleton.elim _ _
    cases heq
    exact hd.1 A i u v
  · intro inst A i s u
    have heq : inst = eqFin := Subsingleton.elim _ _
    cases heq
    exact hd.2.1 A i s u
  · intro A i j he hn
    exact hd.2.2.1 A i j hn he

theorem normalizedAlternatingUnique {K : Type*} [Field K] {n : ℕ}
    (d e : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
    (hd : d (1 : Matrix (Fin n) (Fin n) K) = 1)
    (he : e (1 : Matrix (Fin n) (Fin n) K) = 1) : d = e := by
  have hb : (Pi.basisFun K (Fin n) : Fin n → Fin n → K) = (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [Pi.basisFun_apply]
    · simp [Pi.basisFun_apply, h, Ne.symm h]
  have hd' : d (Pi.basisFun K (Fin n)) = 1 := by simpa only [hb] using hd
  have he' : e (Pi.basisFun K (Fin n)) = 1 := by simpa only [hb] using he
  rw [AlternatingMap.eq_smul_basis_det (Pi.basisFun K (Fin n)) d,
    AlternatingMap.eq_smul_basis_det (Pi.basisFun K (Fin n)) e]
  simp only [hd', he', one_smul]

theorem canonicalDeterminantAxioms {K : Type*} [Field K] (n : ℕ) :
    satisfiesRowDeterminantAxioms n (Matrix.det : Matrix (Fin n) (Fin n) K → K) := by
  exact ⟨det_updateRow_add, det_updateRow_smul,
    fun A i j hn he => det_zero_of_row_eq hn he, det_one⟩

theorem rowDeterminantUnique {K : Type*} [Field K] {n : ℕ}
    (d e : Matrix (Fin n) (Fin n) K → K)
    (hd : satisfiesRowDeterminantAxioms n d) (he : satisfiesRowDeterminantAxioms n e) : d = e := by
  have h := normalizedAlternatingUnique (rowDeterminantAlternating d hd)
    (rowDeterminantAlternating e he) hd.2.2.2 he.2.2.2
  exact congrArg (fun f : (Fin n → K) [⋀^Fin n]→ₗ[K] K => (f : _ → K)) h

theorem rowDeterminantEqualsCanonical {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d) :
    d = Matrix.det := rowDeterminantUnique _ _ hd (canonicalDeterminantAxioms n)

theorem determinantWholeScaling {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d)
    (A : Matrix (Fin n) (Fin n) K) (s : K) : d (s • A) = s^n * d A := by
  rw [rowDeterminantEqualsCanonical d hd]
  simpa using det_smul A s

theorem determinantNullRow {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d)
    (A : Matrix (Fin n) (Fin n) K) (i : Fin n) (h : ∀ j, A i j = 0) : d A = 0 := by
  rw [rowDeterminantEqualsCanonical d hd]
  exact det_eq_zero_of_row_eq_zero i h

theorem determinantRowSwap {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (h : i ≠ j) :
    d (A.submatrix (Equiv.swap i j) id) = -d A := by
  rw [rowDeterminantEqualsCanonical d hd, det_permute]
  simp [Equiv.Perm.sign_swap h]

theorem determinantRowAddition {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (h : i ≠ j) (s : K) :
    d (A.updateRow i (A i + s • A j)) = d A := by
  rw [rowDeterminantEqualsCanonical d hd]
  exact det_updateRow_add_smul_self A h s

theorem determinantUpperTriangular {K : Type*} [Field K] {n : ℕ}
    (d : Matrix (Fin n) (Fin n) K → K) (hd : satisfiesRowDeterminantAxioms n d)
    (A : Matrix (Fin n) (Fin n) K) (h : A.IsUpperTriangular) : d A = ∏ i, A i i := by
  rw [rowDeterminantEqualsCanonical d hd]
  exact det_of_isUpperTriangular h

theorem areaTwoByTwo (a b c d : ℝ) :
    Matrix.det !![a,c;b,d] = a*d-b*c := by simp [det_fin_two]; ring

theorem determinantOneModel {K : Type*} [Field K] (A : Matrix (Fin 1) (Fin 1) K) :
    Matrix.det A = A 0 0 := Matrix.det_fin_one A

theorem determinantTwoModel {K : Type*} [Field K] (a b c d : K) :
    Matrix.det !![a,b;c,d] = a*d-b*c := by simp [det_fin_two]

theorem determinantNotAdditiveAnyField {K : Type*} [Field K] :
    Matrix.det (!![1,0;0,0] + !![0,0;0,1] : Matrix (Fin 2) (Fin 2) K) ≠
      Matrix.det (!![1,0;0,0] : Matrix (Fin 2) (Fin 2) K) + Matrix.det !![0,0;0,1] := by
  simp [det_fin_two]

theorem originalComplexDeterminant :
    Matrix.det (!![0,1,Complex.I;1,Complex.I,1;2,3,4] : Matrix (Fin 3) (Fin 3) ℂ) =
      3*Complex.I := by
  norm_num [det_fin_three, Complex.I_sq]
  ring

end ILab.LinearAlgebra
