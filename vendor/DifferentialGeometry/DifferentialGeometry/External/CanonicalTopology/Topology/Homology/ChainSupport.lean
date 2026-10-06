module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainsIn
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

/-! # Finite support and intersections for the original singular chains -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The geometric carrier submodule is the span of the corresponding
subset of the original proved singular basis. -/
theorem integralSingularChainsIn_eq_span_basis (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A = Submodule.span ℤ
      (integralSingularChainBasis n X ''
        {σ | range (integralSingularSimplexEquiv n X σ) ⊆ A}) := by
  unfold integralSingularChainsIn
  congr 1
  ext c
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, integralSingularChainBasis_apply n σ⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, integralSingularChainBasis_apply n σ⟩

/-- A chain lies in A precisely when each original simplex with nonzero
integer coefficient has its actual image in A. -/
theorem integralSingularChainsIn_mem_iff (n : ℕ) (A : Set X)
    (c : (integralSingularChains X).X n) :
    c ∈ integralSingularChainsIn n A ↔
      ∀ σ : integralSingularSimplex n X, integralSingularChainRepr n X c σ ≠ 0 →
        range (integralSingularSimplexEquiv n X σ) ⊆ A := by
  rw [integralSingularChainsIn_eq_span_basis, (integralSingularChainBasis n X).mem_span_image]
  change (↑(integralSingularChainRepr n X c).support : Set _) ⊆
    {σ | range (integralSingularSimplexEquiv n X σ) ⊆ A} ↔ _
  constructor
  · intro h σ hσ
    exact h (Finsupp.mem_support_iff.mpr hσ)
  · intro h σ hσ
    exact h σ (Finsupp.mem_support_iff.mp hσ)

/-- The support description respects inclusion of actual carriers. -/
theorem integralSingularChainsIn_mono (n : ℕ) {A B : Set X} (h : A ⊆ B) :
    integralSingularChainsIn n A ≤ integralSingularChainsIn n B := by
  intro c hc
  rw [integralSingularChainsIn_mem_iff] at hc ⊢
  exact fun σ hσ => (hc σ hσ).trans h

/-- Intersections of original subspaces give intersections of their actual
singular-chain ranges, by uniqueness of the original basis coefficients. -/
theorem integralSingularChainsIn_inter (n : ℕ) (A B : Set X) :
    integralSingularChainsIn n (A ∩ B) =
      integralSingularChainsIn n A ⊓ integralSingularChainsIn n B := by
  apply le_antisymm
  · exact le_inf (integralSingularChainsIn_mono n inter_subset_left)
      (integralSingularChainsIn_mono n inter_subset_right)
  · intro c hc
    rw [integralSingularChainsIn_mem_iff]
    intro σ hσ
    exact subset_inter ((integralSingularChainsIn_mem_iff n A c).mp hc.1 σ hσ)
      ((integralSingularChainsIn_mem_iff n B c).mp hc.2 σ hσ)

/-- Every actual singular chain is carried by the whole space. -/
theorem integralSingularChainsIn_univ (n : ℕ) :
    integralSingularChainsIn n (univ : Set X) = ⊤ := by
  apply top_unique
  intro c _
  exact (integralSingularChainsIn_mem_iff n univ c).mpr (fun _ _ => subset_univ _)

/-- The empty subspace carries only the original zero chain. -/
theorem integralSingularChainsIn_empty (n : ℕ) :
    integralSingularChainsIn n (∅ : Set X) = ⊥ := by
  apply bot_unique
  intro c hc
  change c = 0
  apply (integralSingularChainRepr n X).injective
  rw [map_zero]
  apply Finsupp.ext
  intro σ
  by_contra hσ
  have h := (integralSingularChainsIn_mem_iff n ∅ c).mp hc σ hσ
  exact (range_nonempty (integralSingularSimplexEquiv n X σ)).ne_empty
    (subset_empty_iff.mp h)

end DifferentialGeometry.Topology
