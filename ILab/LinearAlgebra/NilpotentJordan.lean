import ILab.LinearAlgebra.PrimaryDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-! Holstein §10.3: kernel filtration, complement ingredients, chains and
kernel-profile uniqueness. The complete existence of a compatible family of
complements/Jordan basis is not asserted as a Lean theorem in this file.
In particular, a conditional chain-basis statement is not the existence theorem.
The browser's constructive algorithm is tested separately, not verified by Lean. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module
set_option maxHeartbeats 800000
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local instance : DecidableEq (Module.End K V) := Classical.decEq _

def nilpotentIndex (g : Module.End K V) (h : IsNilpotent g) : ℕ := Nat.find h

theorem nilpotentIndexPower (g : Module.End K V) (h : IsNilpotent g) :
    g ^ nilpotentIndex g h = 0 := Nat.find_spec h

theorem nilpotentIndexMinimal (g : Module.End K V) (h : IsNilpotent g)
    {i : ℕ} (hi : i < nilpotentIndex g h) : g ^ i ≠ 0 := Nat.find_min h hi

def nilpotentKernel (g : Module.End K V) (i : ℕ) : Submodule K V := LinearMap.ker (g^i)

theorem nilpotentKernelZero (g : Module.End K V) : nilpotentKernel g 0 = ⊥ := by
  change LinearMap.ker (LinearMap.id : V →ₗ[K] V) = ⊥
  exact LinearMap.ker_id

theorem nilpotentKernelTop (g : Module.End K V) (h : IsNilpotent g) :
    nilpotentKernel g (nilpotentIndex g h) = ⊤ := by
  simp [nilpotentKernel,nilpotentIndexPower]

theorem nilpotentKernelMonotone (g : Module.End K V) : Monotone (nilpotentKernel g) :=
  fun _ _ h => kernelPowersMonotone g h

theorem nilpotentKernelPreimage (g : Module.End K V) (i : ℕ) :
    (nilpotentKernel g i).comap g = nilpotentKernel g (i+1) := by
  ext v
  simp only [nilpotentKernel,Submodule.mem_comap,LinearMap.mem_ker,pow_succ,
    Module.End.mul_apply]

theorem nilpotentKernelImage (g : Module.End K V) (i : ℕ) :
    ∀ v ∈ nilpotentKernel g (i+1), g v ∈ nilpotentKernel g i := by
  intro v h
  exact (Submodule.mem_comap.mp ((nilpotentKernelPreimage g i).symm ▸ h))

theorem nilpotentKernelStrict (g : Module.End K V) (h : IsNilpotent g)
    {i : ℕ} (hi : i < nilpotentIndex g h) :
    nilpotentKernel g i < nilpotentKernel g (i+1) := by
  apply lt_of_le_of_ne (nilpotentKernelMonotone g (Nat.le_succ i))
  intro he
  have hs := fittingKernelStability g he (nilpotentIndex g h-i)
  have ht : i+(nilpotentIndex g h-i)=nilpotentIndex g h := Nat.add_sub_of_le (Nat.le_of_lt hi)
  rw [ht,nilpotentIndexPower,LinearMap.ker_zero] at hs
  have hp : g^i=0 := LinearMap.ker_eq_top.mp hs
  exact nilpotentIndexMinimal g h hi hp

theorem nilpotentComplementExists (g : Module.End K V) (i : ℕ) :
    ∃ W : Submodule K V, IsCompl (nilpotentKernel g i) W :=
  Submodule.exists_isCompl _

theorem nilpotentInjectiveOnComplement (g : Module.End K V) {W : Submodule K V}
    {i : ℕ} (hi : 0 < i) (hd : Disjoint W (nilpotentKernel g i)) :
    Function.Injective (g.comp W.subtype) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro w hw
  apply Subtype.ext
  have hker : (w : V) ∈ nilpotentKernel g 1 := by simpa [nilpotentKernel] using hw
  have hboth : (w : V) ∈ W ⊓ nilpotentKernel g i :=
    ⟨w.property,nilpotentKernelMonotone g hi hker⟩
  rw [hd.eq_bot] at hboth
  exact hboth

theorem nilpotentImageDisjointLower (g : Module.End K V) {W : Submodule K V}
    (i : ℕ) (hd : Disjoint W (nilpotentKernel g (i+1))) :
    Disjoint (W.map g) (nilpotentKernel g i) := by
  rw [disjoint_iff,Submodule.eq_bot_iff]
  rintro v ⟨⟨w,hw,rfl⟩,hv⟩
  have hn : w ∈ nilpotentKernel g (i+1) := by
    rw [← nilpotentKernelPreimage];exact hv
  have hz : w=0 := by
    have hh : w ∈ W ⊓ nilpotentKernel g (i+1) := ⟨hw,hn⟩
    rw [hd.eq_bot] at hh
    exact hh
  simp [hz]

theorem nilpotentChainStep (g : Module.End K V) (w : V) (a : ℕ) :
    g ((g^a) w) = (g^(a+1)) w := by
  rw [pow_succ'];rfl

theorem nilpotentChainInKernel (g : Module.End K V) (w : V) {d a : ℕ}
    (h : (g^d) w=0) (ha : a ≤ d) : (g^a) w ∈ nilpotentKernel g (d-a) := by
  change (g^(d-a)) ((g^a) w)=0
  rw [← Module.End.mul_apply,← pow_add,Nat.sub_add_cancel ha]
  exact h

theorem nilpotentChainFirstNonzero (g : Module.End K V) (w : V) {d a : ℕ}
    (hd : 0<d) (h : (g^(d-1)) w≠0) (ha : a<d) : (g^a) w≠0 := by
  intro hz
  have he : d-1=(d-1-a)+a := by omega
  apply h
  rw [he,pow_add,Module.End.mul_apply,hz,map_zero]

theorem nilpotentChainInvariant (g : Module.End K V) (w : V) (d : ℕ)
    (hz : (g^d) w=0) :
    ∀ v ∈ Submodule.span K (Set.range (fun i : Fin d => (g^i.val) w)),
      g v ∈ Submodule.span K (Set.range (fun i : Fin d => (g^i.val) w)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    rw [nilpotentChainStep]
    by_cases hi : i.val+1<d
    · exact Submodule.subset_span ⟨⟨i.val+1,hi⟩,rfl⟩
    · have he : i.val+1=d := by omega
      rw [he,hz];exact Submodule.zero_mem _
  | zero => simpa using (Submodule.zero_mem (Submodule.span K (Set.range (fun i : Fin d => (g^i.val) w))))
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- Signed second difference, avoiding truncated natural subtraction. -/
def kernelProfileMultiplicity (u : ℕ → ℤ) (i : ℕ) : ℤ := 2*u (i+1)-u i-u (i+2)

theorem kernelProfileDifference (u : ℕ → ℤ) (i : ℕ) :
    kernelProfileMultiplicity u i = (u (i+1)-u i)-(u (i+2)-u (i+1)) := by
  unfold kernelProfileMultiplicity;ring

theorem kernelProfileNonnegative (u : ℕ → ℤ) (i : ℕ)
    (h : u (i+2)-u (i+1) ≤ u (i+1)-u i) : 0 ≤ kernelProfileMultiplicity u i := by
  rw [kernelProfileDifference];omega

theorem kernelProfileUnique (u : ℕ → ℤ) (k l : ℕ → ℤ)
    (hk : ∀ i, k i=(u (i+1)-u i)-(u (i+2)-u (i+1)))
    (hl : ∀ i, l i=(u (i+1)-u i)-(u (i+2)-u (i+1))) : k=l := by
  funext i;rw [hk,hl]

theorem kernelProfileWeightedSum (u : ℕ → ℤ) (d : ℕ) :
    (∑ i ∈ Finset.range d, ((i+1 : ℕ) : ℤ)*kernelProfileMultiplicity u i) =
      u d-u 0-(d : ℤ)*(u (d+1)-u d) := by
  induction d with
  | zero => simp
  | succ d hd =>
    rw [Finset.sum_range_succ,hd]
    unfold kernelProfileMultiplicity
    push_cast
    ring

theorem kernelProfileTotalDimension (u : ℕ → ℤ) (d : ℕ) (h0 : u 0=0)
    (hs : u (d+1)=u d) :
    (∑ i ∈ Finset.range d, ((i+1 : ℕ) : ℤ)*kernelProfileMultiplicity u i) = u d := by
  rw [kernelProfileWeightedSum,h0,hs];ring

def nilpotentKernelDimensions [FiniteDimensional K V] (g : Module.End K V) (i : ℕ) : ℤ :=
  (finrank K (nilpotentKernel g i) : ℤ)

/-- An actual kernel-dimension identity. Identifying the signed coefficients with
nonnegative Jordan block counts still requires the compatible-basis theorem. -/
theorem nilpotentKernelProfileWeightedDimension [FiniteDimensional K V]
    (g : Module.End K V) (h : IsNilpotent g) :
    (∑ i ∈ Finset.range (nilpotentIndex g h), ((i+1 : ℕ) : ℤ)*
      kernelProfileMultiplicity (nilpotentKernelDimensions g) i) = (finrank K V : ℤ) := by
  have h0 : nilpotentKernelDimensions g 0=0 := by
    simp [nilpotentKernelDimensions,nilpotentKernelZero]
  have htop : nilpotentKernelDimensions g (nilpotentIndex g h)=(finrank K V : ℤ) := by
    unfold nilpotentKernelDimensions
    rw [nilpotentKernelTop g h]
    simp
  have hs : nilpotentKernelDimensions g (nilpotentIndex g h+1)=
      nilpotentKernelDimensions g (nilpotentIndex g h) := by
    have hp : g^(nilpotentIndex g h+1)=0 := by
      rw [pow_succ,nilpotentIndexPower,zero_mul]
    unfold nilpotentKernelDimensions nilpotentKernel
    rw [hp,nilpotentIndexPower g h]
  rw [kernelProfileTotalDimension _ _ h0 hs,htop]

theorem nilpotentBlockPowerZero (r : ℕ) : (jordanBlock (0 : K) r)^r=0 := by
  apply strictUpperNilpotent
  · exact jordanBlockUpper 0 r
  · intro i;simpa using jordanBlockDiagonal (0 : K) r i

theorem jordanShiftConjugation {r : ℕ} (a : K) (N T S : Matrix (Fin r) (Fin r) K)
    (h : T*S=1) : T*(a • (1 : Matrix (Fin r) (Fin r) K)+N)*S = a • 1+T*N*S := by
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,h]

/-- This is a basis-change certificate, not an existence claim. -/
theorem jordanBasisCertificate {r : ℕ} (A B S J : Matrix (Fin r) (Fin r) K)
    (hSB : S*B=1) (hAB : A*B=B*J) : S*A*B=J := by
  rw [Matrix.mul_assoc,hAB,← Matrix.mul_assoc,hSB,Matrix.one_mul]

def nilpotentExampleThree : Matrix (Fin 3) (Fin 3) ℚ := !![-1,1,0;-1,1,1;0,0,0]

theorem nilpotentExampleCube : nilpotentExampleThree^3=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [nilpotentExampleThree,pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

theorem nilpotentExampleSquareNonzero : nilpotentExampleThree^2≠0 := by
  intro h
  have := congrFun (congrFun h 0) 2
  norm_num [nilpotentExampleThree,pow_two,Matrix.mul_apply,Fin.sum_univ_succ] at this

end ILab.LinearAlgebra
