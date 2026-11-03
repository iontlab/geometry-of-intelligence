import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Lean.Elab.Tactic.Omega

/-!
Holstein, Lineare Algebra 2023/24, printed pp. 71–73.
The field and finiteness assumptions are explicit. Natural-valued finrank
statements are used only with the corresponding finite-dimensional hypotheses.
The cardinal-valued rank and product-dimension statements also cover infinite
dimension. A binary direct sum is represented by the canonically equivalent
product V × W.
-/

namespace ILab.LinearAlgebra

open Module Function
universe u v w
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- Definition 4.3.1: dimension of the image, without a finiteness restriction. -/
noncomputable def rank (f : V →ₗ[K] W) : Cardinal.{w} :=
  Module.rank K (LinearMap.range f)

/-- The finite-dimensional numerical version used in 4.3.4 and 4.3.5. -/
noncomputable def finiteRank (f : V →ₗ[K] W) : ℕ :=
  finrank K (LinearMap.range f)

/-- The quotient by the kernel is linearly equivalent to the image. -/
noncomputable def quotientKernelEquivImage (f : V →ₗ[K] W) :
    (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f :=
  f.quotKerEquivRange

theorem quotientKernelDimension [FiniteDimensional K V] (f : V →ₗ[K] W) :
    finrank K (V ⧸ LinearMap.ker f) = finiteRank f :=
  (quotientKernelEquivImage f).finrank_eq

/-- Satz 4.3.4. W need not be finite-dimensional. -/
theorem rankNullity [FiniteDimensional K V] (f : V →ₗ[K] W) :
    finrank K V = finrank K (LinearMap.ker f) + finiteRank f := by
  simpa [finiteRank, Nat.add_comm] using
    (LinearMap.finrank_range_add_finrank_ker f).symm

/-- The quotient-based proof exposes the same dimension mechanism explicitly. -/
theorem rankNullityViaQuotient [FiniteDimensional K V] (f : V →ₗ[K] W) :
    finrank K V = finrank K (LinearMap.ker f) + finiteRank f := by
  rw [← quotientKernelDimension f, Nat.add_comm]
  exact (Submodule.finrank_quotient_add_finrank (LinearMap.ker f)).symm

theorem injectiveIffKernelZero (f : V →ₗ[K] W) :
    Injective f ↔ LinearMap.ker f = ⊥ :=
  LinearMap.ker_eq_bot.symm

theorem surjectiveIffImageWhole (f : V →ₗ[K] W) :
    Surjective f ↔ LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top.symm

/-- Korollar 4.3.5, with an actual proof dependency on rankNullity. -/
theorem injectiveIffSurjective [FiniteDimensional K V] [FiniteDimensional K W]
    (h : finrank K V = finrank K W) (f : V →ₗ[K] W) :
    Injective f ↔ Surjective f := by
  have hd := rankNullity f
  change finrank K V = finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) at hd
  constructor
  · intro hf
    have hk := (injectiveIffKernelZero f).mp hf
    have hr : finrank K (LinearMap.range f) = finrank K W := by
      rw [hk, finrank_bot, zero_add] at hd
      exact hd.symm.trans h
    exact (surjectiveIffImageWhole f).mpr (Submodule.eq_top_of_finrank_eq hr)
  · intro hf
    have hr := (surjectiveIffImageWhole f).mp hf
    have hk : finrank K (LinearMap.ker f) = 0 := by
      rw [hr, finrank_top, h] at hd
      omega
    exact (injectiveIffKernelZero f).mpr (Submodule.finrank_eq_zero.mp hk)

theorem injectiveIffBijective [FiniteDimensional K V] [FiniteDimensional K W]
    (h : finrank K V = finrank K W) (f : V →ₗ[K] W) :
    Injective f ↔ Bijective f :=
  ⟨fun hf => ⟨hf, (injectiveIffSurjective h f).mp hf⟩, fun hf => hf.1⟩

theorem surjectiveIffBijective [FiniteDimensional K V] [FiniteDimensional K W]
    (h : finrank K V = finrank K W) (f : V →ₗ[K] W) :
    Surjective f ↔ Bijective f :=
  ⟨fun hf => ⟨(injectiveIffSurjective h f).mpr hf, hf⟩, fun hf => hf.2⟩

/-- All three conditions of Korollar 4.3.5 in one certificate. -/
theorem injectiveSurjectiveBijective [FiniteDimensional K V] [FiniteDimensional K W]
    (h : finrank K V = finrank K W) (f : V →ₗ[K] W) :
    (Injective f ↔ Surjective f) ∧ (Surjective f ↔ Bijective f) :=
  ⟨injectiveIffSurjective h f, surjectiveIffBijective h f⟩

/-- Korollar 4.3.7: n vectors in dimension n. -/
theorem independentIffSpanning [FiniteDimensional K V] {n : ℕ}
    (h : n = finrank K V) (b : Fin n → V) :
    LinearIndependent K b ↔ Submodule.span K (Set.range b) = ⊤ := by
  constructor
  · intro hb
    apply Submodule.eq_top_of_finrank_eq
    simpa [h] using (finrank_span_eq_card hb)
  · intro hb
    exact linearIndependent_of_top_le_span_of_card_eq_finrank
      (by rw [hb]) (by simpa using h)

theorem basisCriterion [FiniteDimensional K V] {n : ℕ}
    (h : n = finrank K V) (b : Fin n → V) :
    ((∃ B : Basis (Fin n) K V, ∀ i, B i = b i) ↔ LinearIndependent K b) ∧
      (LinearIndependent K b ↔ Submodule.span K (Set.range b) = ⊤) := by
  refine ⟨⟨?_, ?_⟩, independentIffSpanning h b⟩
  · rintro ⟨B, hB⟩
    have he : (B : Fin n → V) = b := funext hB
    rw [← he]
    exact B.linearIndependent
  · intro hb
    have hs := (independentIffSpanning h b).mp hb
    refine ⟨Basis.mk hb (by rw [hs]), ?_⟩
    intro i
    exact Basis.mk_apply _ _ i

/-- Satz 4.3.8, classification by finite dimension. -/
theorem isomorphicIffDimension [FiniteDimensional K V] [FiniteDimensional K W] :
    Nonempty (V ≃ₗ[K] W) ↔ finrank K V = finrank K W :=
  ⟨fun ⟨e⟩ => e.finrank_eq, fun h => ⟨LinearEquiv.ofFinrankEq V W h⟩⟩

noncomputable def coordinateEquivalence [FiniteDimensional K V] :
    V ≃ₗ[K] (Fin (finrank K V) → K) :=
  (Module.finBasis K V).equivFun

/-- Lemma 4.3.9, finite-dimensional numerical statement. -/
theorem directSumDimension [FiniteDimensional K V] [FiniteDimensional K W] :
    finrank K (V × W) = finrank K V + finrank K W :=
  Module.finrank_prod

/-- Lemma 4.3.9 without finite-dimensional assumptions, in a common universe. -/
theorem directSumCardinalDimension {W' : Type v} [AddCommGroup W'] [Module K W'] :
    Module.rank K (V × W') = Module.rank K V + Module.rank K W' :=
  rank_prod'

/-- Satz 4.3.10 in its balanced form. Only U and T are assumed finite. -/
theorem sumIntersectionDimension (U T : Submodule K V)
    [FiniteDimensional K U] [FiniteDimensional K T] :
    finrank K (U ⊔ T : Submodule K V) + finrank K (U ⊓ T : Submodule K V) =
      finrank K U + finrank K T :=
  Submodule.finrank_sup_add_finrank_inf_eq U T

/-- Submodule supremum is U+T; infimum is U∩T. -/
theorem subspaceSumDimension (U T : Submodule K V)
    [FiniteDimensional K U] [FiniteDimensional K T] :
    finrank K (U ⊔ T : Submodule K V) =
      finrank K U + finrank K T - finrank K (U ⊓ T : Submodule K V) :=
  Nat.eq_sub_of_add_eq (sumIntersectionDimension U T)

end ILab.LinearAlgebra
