import ILab.LinearAlgebra.PermutationsDeterminants
import ILab.LinearAlgebra.CoordinateChanges
import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Holstein §§7.6–7.8 (LA-P026). Fin n is the ordered index set 0,...,n-1.
coordinateChange a b is Holstein T_b^a: OLD a coordinates to NEW b coordinates.
The actual quotient of ordered bases is used, not just two scalar signs.
Positive n is essential for surjectivity onto both orientation rays.
Minor statements below include the general nonzero-minor lower bound and
the vanishing of all minors larger than the rank. Their converse is not claimed.
Trace identities use arbitrary fields, not just the real orientation setting. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module Matrix
variable {n m k : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

def SameHolsteinOrientation (a b : Basis (Fin n) ℝ V) : Prop :=
  0 < (coordinateChange a b).det

theorem sameOrientationIffRay (a b : Basis (Fin n) ℝ V) :
    SameHolsteinOrientation a b ↔ a.orientation = b.orientation := by
  rw [SameHolsteinOrientation, coordinateChangeConvention]
  simpa only [Basis.det_apply, eq_comm] using (b.orientation_eq_iff_det_pos a).symm

theorem sameOrientationRefl (a : Basis (Fin n) ℝ V) : SameHolsteinOrientation a a :=
  (sameOrientationIffRay a a).mpr rfl

theorem sameOrientationSymm {a b : Basis (Fin n) ℝ V}
    (h : SameHolsteinOrientation a b) : SameHolsteinOrientation b a :=
  (sameOrientationIffRay b a).mpr ((sameOrientationIffRay a b).mp h).symm

theorem sameOrientationTrans {a b c : Basis (Fin n) ℝ V}
    (h₁ : SameHolsteinOrientation a b) (h₂ : SameHolsteinOrientation b c) :
    SameHolsteinOrientation a c :=
  (sameOrientationIffRay a c).mpr (((sameOrientationIffRay a b).mp h₁).trans
    ((sameOrientationIffRay b c).mp h₂))

def orderedBasisOrientationSetoid : Setoid (Basis (Fin n) ℝ V) where
  r := SameHolsteinOrientation
  iseqv := ⟨sameOrientationRefl, fun h => sameOrientationSymm h,
    fun h₁ h₂ => sameOrientationTrans h₁ h₂⟩

def HolsteinOrientation (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  Quotient (orderedBasisOrientationSetoid (n := n) (V := V))

def orientationClassRay : HolsteinOrientation n V → Orientation ℝ V (Fin n) :=
  Quotient.lift (fun a => a.orientation) (fun a b h => (sameOrientationIffRay a b).mp h)

theorem orientationClassRayInjective :
    Function.Injective (orientationClassRay (n := n) (V := V)) := by
  intro x y
  induction x using Quotient.inductionOn with | h a =>
    induction y using Quotient.inductionOn with | h b =>
      intro h
      exact Quotient.sound ((sameOrientationIffRay a b).mpr h)

theorem orientationClassRaySurjective [Nonempty (Fin n)] (a : Basis (Fin n) ℝ V) :
    Function.Surjective (orientationClassRay (n := n) (V := V)) := by
  intro o
  exact ⟨Quotient.mk _ (a.adjustToOrientation o), a.orientation_adjustToOrientation o⟩

def orientationQuotientEquivRay [Nonempty (Fin n)] (a : Basis (Fin n) ℝ V) :
    HolsteinOrientation n V ≃ Orientation ℝ V (Fin n) :=
  Equiv.ofBijective orientationClassRay
    ⟨orientationClassRayInjective, orientationClassRaySurjective a⟩

def orientationRayEquivBool (a : Basis (Fin n) ℝ V) : Orientation ℝ V (Fin n) ≃ Bool := by
  classical
  refine Equiv.ofBijective (fun o => decide (o = a.orientation)) ⟨?_, ?_⟩
  · intro x y h
    by_cases hx : x = a.orientation
    · have hy : y = a.orientation := of_decide_eq_true (by simpa [hx] using h.symm)
      exact hx.trans hy.symm
    · have hy : y ≠ a.orientation := by
        intro hy
        simpa [hx, hy] using h
      exact ((a.orientation_ne_iff_eq_neg x).mp hx).trans
        ((a.orientation_ne_iff_eq_neg y).mp hy).symm
  · intro b
    cases b
    · refine ⟨-a.orientation, ?_⟩
      simp only [decide_eq_false_iff_not]
      exact (Module.Ray.ne_neg_self a.orientation).symm
    · exact ⟨a.orientation, by simp⟩

def orientationQuotientEquivBool [Nonempty (Fin n)] (a : Basis (Fin n) ℝ V) :
    HolsteinOrientation n V ≃ Bool :=
  (orientationQuotientEquivRay a).trans (orientationRayEquivBool a)

theorem exactlyTwoOrientationClasses [Nonempty (Fin n)] (a : Basis (Fin n) ℝ V) :
    Nat.card (HolsteinOrientation n V) = 2 := by
  rw [Nat.card_congr (orientationQuotientEquivBool a)]
  simp

theorem negatingOneBasisVectorChangesOrientation (a : Basis (Fin n) ℝ V) (i : Fin n) :
    ¬ SameHolsteinOrientation a (a.unitsSMul (Function.update 1 i (-1))) := by
  rw [sameOrientationIffRay, a.orientation_neg_single]
  exact Module.Ray.ne_neg_self _

theorem basisMapPreservesOrientation (a : Basis (Fin n) ℝ V) (f : V ≃ₗ[ℝ] V) :
    SameHolsteinOrientation (a.map f) a ↔ 0 < LinearMap.det (f : V →ₗ[ℝ] V) := by
  rw [sameOrientationIffRay]
  exact a.orientation_comp_linearEquiv_eq_iff_det_pos f

def orientationPreservingAutomorphisms : Subgroup (V ≃ₗ[ℝ] V) where
  carrier := {f | 0 < (LinearEquiv.det f : ℝ)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change 0 < (LinearEquiv.det a : ℝ) at ha
    change 0 < (LinearEquiv.det b : ℝ) at hb
    change 0 < (LinearEquiv.det (a*b) : ℝ)
    rw [map_mul]
    exact mul_pos ha hb
  inv_mem' := by
    intro a ha
    change 0 < (LinearEquiv.det a : ℝ) at ha
    change 0 < (LinearEquiv.det a⁻¹ : ℝ)
    simpa only [map_inv, Units.val_inv_eq_inv_val] using inv_pos.mpr ha

theorem orientationPreservingMembership (f : V ≃ₗ[ℝ] V) :
    f ∈ orientationPreservingAutomorphisms ↔ 0 < LinearMap.det (f : V →ₗ[ℝ] V) := by
  change (0 < (LinearEquiv.det f : ℝ)) ↔ _
  rw [LinearEquiv.coe_det]

section MinorsTrace
variable {K : Type*} [Field K]

def selectedMinor (A : Matrix (Fin m) (Fin n) K)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n) : K :=
  (A.submatrix rows cols).det

theorem nonzeroMinorBoundsRank (A : Matrix (Fin m) (Fin n) K)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n)
    (h : selectedMinor A rows cols ≠ 0) : k ≤ A.rank := by
  have hr := Matrix.rank_of_det_ne_zero h
  simpa using hr.symm.le.trans (Matrix.rank_submatrix_le A rows cols)

theorem minorsAboveRankVanish (A : Matrix (Fin m) (Fin n) K)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n) (h : A.rank < k) :
    selectedMinor A rows cols = 0 := by
  by_contra hz
  exact (not_le_of_gt h) (nonzeroMinorBoundsRank A rows cols hz)

theorem rectangularProductDetZero (A B : Matrix (Fin m) (Fin n) K) (h : n < m) :
    (A * B.transpose).det = 0 := by
  by_contra hz
  have hr := Matrix.rank_of_det_ne_zero hz
  have hle := (Matrix.rank_mul_le_left A B.transpose).trans A.rank_le_width
  simp only [Fintype.card_fin] at hr hle
  omega

def holsteinTrace (A : Matrix (Fin n) (Fin n) K) : K := A.trace

theorem traceLinearCombination (A B : Matrix (Fin n) (Fin n) K) (a b : K) :
    holsteinTrace (a • A + b • B) = a * holsteinTrace A + b * holsteinTrace B := by
  simp [holsteinTrace, Matrix.trace_add, Matrix.trace_smul]

theorem traceCyclicRectangular (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K) : (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

theorem traceSimilarity (A : Matrix (Fin n) (Fin n) K) (S : (Matrix (Fin n) (Fin n) K)ˣ) :
    ((S : Matrix (Fin n) (Fin n) K) * A * (↑(S⁻¹) : Matrix (Fin n) (Fin n) K)).trace = A.trace :=
  Matrix.trace_units_conj S A

theorem traceTranspose (A : Matrix (Fin n) (Fin n) K) : A.transpose.trace = A.trace :=
  Matrix.trace_transpose A

variable {M : Type*} [AddCommGroup M] [Module K M]

theorem traceIndependentOfBasis (a b : Basis (Fin n) K M) (f : M →ₗ[K] M) :
    (LinearMap.toMatrix a a f).trace = (LinearMap.toMatrix b b f).trace := by
  rw [← LinearMap.trace_eq_matrix_trace K a f, ← LinearMap.trace_eq_matrix_trace K b f]

theorem endomorphismTraceCoordinates (a : Basis (Fin n) K M) (f : M →ₗ[K] M) :
    LinearMap.trace K M f = (LinearMap.toMatrix a a f).trace :=
  LinearMap.trace_eq_matrix_trace K a f

end MinorsTrace
end ILab.LinearAlgebra
