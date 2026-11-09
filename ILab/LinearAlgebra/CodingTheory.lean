import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Holstein Kapitel 8. Corrected mathematical statements are explicitly separated
from the unchanged original in the learning unit. No assertion about the JS engine. -/
namespace ILab.LinearAlgebra
abbrev BinaryWord (n : ℕ) := Fin n → ZMod 2
def codingDistance {n : ℕ} (v w : BinaryWord n) : ℕ := hammingDist v w
theorem codingDistance_card {n : ℕ} (v w : BinaryWord n) :
    codingDistance v w = (Finset.univ.filter (fun i => v i ≠ w i)).card := rfl
theorem codingDistance_zero {n : ℕ} (v w : BinaryWord n) :
    codingDistance v w = 0 ↔ v = w := hammingDist_eq_zero
theorem codingDistance_symm {n : ℕ} (v w : BinaryWord n) :
    codingDistance v w = codingDistance w v := hammingDist_comm v w
theorem codingDistance_triangle {n : ℕ} (u v w : BinaryWord n) :
    codingDistance u w ≤ codingDistance u v + codingDistance v w := hammingDist_triangle u v w
theorem codingDistance_translate {n : ℕ} (v w u : BinaryWord n) :
    codingDistance (v+u) (w+u) = codingDistance v w := by
  exact hammingDist_comp (fun i x => x + u i) (fun i x y h => add_right_cancel h)

def CorrectingCode {n : ℕ} (C : Set (BinaryWord n)) (t : ℕ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2*t+1 ≤ codingDistance u v
theorem codingUniqueNearby {n t : ℕ} {C : Set (BinaryWord n)}
    (hC : CorrectingCode C t) {v w₁ w₂ : BinaryWord n}
    (h₁ : w₁ ∈ C) (h₂ : w₂ ∈ C)
    (d₁ : codingDistance v w₁ ≤ t) (d₂ : codingDistance v w₂ ≤ t) : w₁=w₂ := by
  by_contra h
  have lo := hC w₁ h₁ w₂ h₂ h
  have hi := codingDistance_triangle w₁ v w₂
  rw [codingDistance_symm w₁ v] at hi
  omega
abbrev BinaryLinearCode (n : ℕ) := Submodule (ZMod 2) (BinaryWord n)
theorem codingLinearClosure {n : ℕ} (C : BinaryLinearCode n)
    (u v : BinaryWord n) (a : ZMod 2) (hu : u ∈ C) (hv : v ∈ C) :
    (0 : BinaryWord n) ∈ C ∧ u+v ∈ C ∧ a • u ∈ C :=
  ⟨C.zero_mem,C.add_mem hu hv,C.smul_mem a hu⟩
noncomputable def codingControl {n : ℕ} (C : BinaryLinearCode n) := C.mkQ
theorem codingControlKernel {n : ℕ} (C : BinaryLinearCode n) :
    LinearMap.ker (codingControl C) = C := Submodule.ker_mkQ C
theorem codingControlSurjective {n : ℕ} (C : BinaryLinearCode n) :
    Function.Surjective (codingControl C) := Submodule.mkQ_surjective C
theorem codingSyndromeUnique {n r t : ℕ} (F : BinaryWord n →ₗ[ZMod 2] BinaryWord r)
    (hC : CorrectingCode (LinearMap.ker F : Set (BinaryWord n)) t)
    {x x' : BinaryWord n} (hy : F x = F x')
    (hx : codingDistance x 0 ≤ t) (hx' : codingDistance x' 0 ≤ t) : x=x' := by
  have hk : x-x' ∈ LinearMap.ker F := by simp [LinearMap.mem_ker,map_sub,hy]
  by_contra ne
  have nz : x-x' ≠ 0 := sub_ne_zero.mpr ne
  have lo := hC (x-x') hk 0 (by simp) nz
  have hi := codingDistance_triangle x 0 x'
  have hd : codingDistance (x-x') 0 = codingDistance x x' := by
    have h := codingDistance_translate x x' (-x')
    simpa [sub_eq_add_neg] using h
  rw [hd] at lo
  rw [codingDistance_symm 0 x'] at hi
  omega
theorem codingDecoderInKernel {n r : ℕ} (F : BinaryWord n →ₗ[ZMod 2] BinaryWord r)
    (v x : BinaryWord n) (h : F v = F x) : v-x ∈ LinearMap.ker F := by
  simp [LinearMap.mem_ker,map_sub,h]
theorem codingDecoderBudget {n r t : ℕ} (F : BinaryWord n →ₗ[ZMod 2] BinaryWord r)
    (hC : CorrectingCode (LinearMap.ker F : Set (BinaryWord n)) t)
    {c e x : BinaryWord n} (hc : c ∈ LinearMap.ker F)
    (he : codingDistance e 0 ≤ t) (hx : codingDistance x 0 ≤ t)
    (hs : F (c+e) = F x) : c+e-x=c := by
  have hy : F e=F x := by simpa [map_add,LinearMap.mem_ker.mp hc] using hs
  have eq := codingSyndromeUnique F hC hy he hx
  rw [← eq]; abel
def hammingGenerator : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  !![1,0,0,0,1,1,0; 0,1,0,0,1,0,1; 0,0,1,0,0,1,1; 0,0,0,1,1,1,1]
def hammingControl : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1,1,0,1,1,0,0; 1,0,1,1,0,1,0; 0,1,1,1,0,0,1]
def hammingEncode (m : BinaryWord 4) : BinaryWord 7 := Matrix.vecMul m hammingGenerator
def hammingSyndrome (v : BinaryWord 7) : BinaryWord 3 := hammingControl.mulVec v
theorem hammingControlGenerator : hammingControl * hammingGenerator.transpose = 0 := by
  decide
theorem hammingSystematic (m : BinaryWord 4) (i : Fin 4) :
    hammingEncode m ⟨i.val,by omega⟩ = m i := by
  fin_cases i <;> simp [hammingEncode,hammingGenerator,Matrix.vecMul, dotProduct,Fin.sum_univ_succ]
theorem hammingEncodeInjective : Function.Injective hammingEncode := by
  intro m m' h; funext i
  have hi := congrFun h ⟨i.val,by omega⟩
  simpa only [hammingSystematic] using hi
theorem hammingEncodeSyndrome (m : BinaryWord 4) : hammingSyndrome (hammingEncode m) = 0 := by
  ext i; fin_cases i <;>
    simp [hammingSyndrome,hammingEncode,hammingControl,hammingGenerator,Matrix.mulVec,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] <;> ring_nf <;> simp only [show (2 : ZMod 2)=0 from rfl,mul_zero,add_zero]
theorem hammingKernelWords (v : BinaryWord 7) :
    hammingSyndrome v = 0 ↔ ∃ m, hammingEncode m = v := by
  constructor
  · intro hv
    refine ⟨fun i => v ⟨i.val,by omega⟩,?_⟩
    have h0 := congrFun hv 0; have h1 := congrFun hv 1; have h2 := congrFun hv 2
    simp [hammingSyndrome,hammingControl,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
    ext i; fin_cases i <;> simp [hammingEncode,hammingGenerator,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]
    · linear_combination (norm := ring_nf) h0
      simp only [show (2 : ZMod 2)=0 from rfl,mul_zero,neg_zero]
    · linear_combination (norm := ring_nf) h1
      simp only [show (2 : ZMod 2)=0 from rfl,mul_zero,neg_zero]
    · linear_combination (norm := ring_nf) h2
      simp only [show (2 : ZMod 2)=0 from rfl,mul_zero,neg_zero]
  · rintro ⟨m,rfl⟩; exact hammingEncodeSyndrome m
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem hammingNonzeroWeight : ∀ m : BinaryWord 4,
    m ≠ 0 → 3 ≤ codingDistance (hammingEncode m) 0 := by decide
def hammingEncodeLinear : BinaryWord 4 →ₗ[ZMod 2] BinaryWord 7 where
  toFun := hammingEncode
  map_add' := by intro a b; exact Matrix.add_vecMul hammingGenerator a b
  map_smul' := by intro a b; exact Matrix.smul_vecMul a b hammingGenerator
noncomputable def hammingCheckLinear : BinaryWord 7 →ₗ[ZMod 2] BinaryWord 3 := hammingControl.mulVecLin
noncomputable def hammingLinearCode : BinaryLinearCode 7 := LinearMap.range hammingEncodeLinear
theorem hammingCodeDimension : Module.finrank (ZMod 2) hammingLinearCode = 4 := by
  rw [hammingLinearCode, LinearMap.finrank_range_of_inj hammingEncodeInjective]
  simp [BinaryWord]
theorem hammingCodeKernel : LinearMap.ker hammingCheckLinear = hammingLinearCode := by
  ext v; exact hammingKernelWords v
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem hammingPairDistance : ∀ m m' : BinaryWord 4,
    m ≠ m' → 3 ≤ codingDistance (hammingEncode m) (hammingEncode m') := by decide
theorem hammingCorrecting : CorrectingCode (hammingLinearCode : Set (BinaryWord 7)) 1 := by
  intro u hu v hv h
  obtain ⟨m,rfl⟩ := hu
  obtain ⟨m',rfl⟩ := hv
  exact hammingPairDistance m m' (fun eq => h (congrArg hammingEncode eq))
def hammingError (y : BinaryWord 3) : BinaryWord 7 :=
  if y=0 then 0 else fun i => if (fun j => hammingControl j i)=y then 1 else 0
def hammingDecode (v : BinaryWord 7) := v-hammingError (hammingSyndrome v)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem hammingSyndromeTable : ∀ y : BinaryWord 3,
    hammingSyndrome (hammingError y) = y ∧ codingDistance (hammingError y) 0 ≤ 1 := by decide
theorem hammingDecodeWithinBudget (c e : BinaryWord 7)
    (hc : c ∈ hammingLinearCode) (he : codingDistance e 0 ≤ 1) : hammingDecode (c+e)=c := by
  apply codingDecoderBudget hammingCheckLinear
  · simpa only [hammingCodeKernel] using hammingCorrecting
  · simpa only [hammingCodeKernel] using hc
  · exact he
  · exact (hammingSyndromeTable (hammingSyndrome (c+e))).2
  · exact (hammingSyndromeTable (hammingSyndrome (c+e))).1.symm
theorem codingCardinality {n : ℕ} (C : BinaryLinearCode n) [Fintype C] :
    Fintype.card C = 2 ^ Module.finrank (ZMod 2) C := by
  simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := C))
noncomputable def codingQuotientCoordinates {n : ℕ} (C : BinaryLinearCode n) :
    (BinaryWord n ⧸ C) ≃ₗ[ZMod 2] BinaryWord (n-Module.finrank (ZMod 2) C) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [Submodule.finrank_quotient]; simp [BinaryWord])
noncomputable def codingCoordinateControl {n : ℕ} (C : BinaryLinearCode n) :=
  (codingQuotientCoordinates C).toLinearMap.comp C.mkQ
theorem codingCoordinateControlKernel {n : ℕ} (C : BinaryLinearCode n) :
    LinearMap.ker (codingCoordinateControl C) = C := by
  ext v; simp [codingCoordinateControl]
theorem codingCoordinateControlSurjective {n : ℕ} (C : BinaryLinearCode n) :
    Function.Surjective (codingCoordinateControl C) :=
  (codingQuotientCoordinates C).surjective.comp C.mkQ_surjective
theorem hammingDistanceWitness : codingDistance (hammingEncode ![1,0,0,0]) 0 = 3 := by decide
theorem codingSyndromeError {n r : ℕ} (F : BinaryWord n →ₗ[ZMod 2] BinaryWord r)
    (c e : BinaryWord n) (hc : c ∈ LinearMap.ker F) : F (c+e)=F e := by
  simp [map_add,LinearMap.mem_ker.mp hc]
end ILab.LinearAlgebra

