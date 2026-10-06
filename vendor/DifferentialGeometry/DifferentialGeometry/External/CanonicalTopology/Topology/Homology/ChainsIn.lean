module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps

@[expose] public section

/-! # Actual singular chains carried by a prescribed subspace -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Chains carried by A are spanned by original simplices whose actual
continuous maps have image in A. -/
def integralSingularChainsIn (n : ℕ) (A : Set X) :
    Submodule ℤ ((integralSingularChains X).X n) :=
  Submodule.span ℤ {c | ∃ σ : integralSingularSimplex n X,
    range (integralSingularSimplexEquiv n X σ) ⊆ A ∧ c = integralSimplexChain n σ}

/-- The same actual simplex factors through its original image subspace. -/
def integralSingularSimplexRestriction (n : ℕ) (A : Set X) (σ : integralSingularSimplex n X)
    (hσ : range (integralSingularSimplexEquiv n X σ) ⊆ A) : integralSingularSimplex n A :=
  (integralSingularSimplexEquiv n A).symm
    ⟨fun t => ⟨integralSingularSimplexEquiv n X σ t, hσ ⟨t, rfl⟩⟩,
      (integralSingularSimplexEquiv n X σ).continuous.subtype_mk _⟩

/-- Inclusion recovers the same simplex with its exact original parameters. -/
theorem integralSingularSimplexRestriction_inclusion (n : ℕ) (A : Set X)
    (σ : integralSingularSimplex n X) (hσ : range (integralSingularSimplexEquiv n X σ) ⊆ A) :
    integralSingularSimplexMap n (singularSubspaceInclusion A)
      (integralSingularSimplexRestriction n A σ hσ) = σ := by
  apply (integralSingularSimplexEquiv n X).injective
  rw [integralSingularSimplexMap_apply]
  unfold integralSingularSimplexRestriction
  rw [Equiv.apply_symm_apply]
  rfl

/-- The support description is exactly the range of the original subspace
inclusion on actual singular chains. -/
theorem integralSingularChainsIn_eq_range (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A =
      LinearMap.range ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro c ⟨σ, hσ, rfl⟩
    refine ⟨integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ), ?_⟩
    rw [integralSimplexChain_map, integralSingularSimplexRestriction_inclusion]
  · have htop : Submodule.comap
        ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
          (integralSingularChainsIn n A) = ⊤ := by
      apply top_unique
      rw [← (integralSingularChainBasis n A).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      change (integralSingularChainMap (singularSubspaceInclusion A)).f n
        (integralSingularChainBasis n A σ) ∈ integralSingularChainsIn n A
      rw [integralSingularChainBasis_apply, integralSimplexChain_map]
      apply Submodule.subset_span
      refine ⟨integralSingularSimplexMap n (singularSubspaceInclusion A) σ, ?_, rfl⟩
      rintro _ ⟨t, rfl⟩
      rw [integralSingularSimplexMap_apply]
      exact (integralSingularSimplexEquiv n A σ t).property
    rintro c ⟨b, rfl⟩
    exact show b ∈ Submodule.comap
      ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
        (integralSingularChainsIn n A) from htop.symm ▸ Submodule.mem_top

/-- The original boundary preserves the actual carrier. -/
theorem integralSingularChainsIn_boundary (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X (n + 1)} (hc : c ∈ integralSingularChainsIn (n + 1) A) :
    (integralSingularChains X).d (n + 1) n c ∈ integralSingularChainsIn n A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  refine ⟨(integralSingularChains A).d (n + 1) n b, ?_⟩
  exact (congrArg (fun h : (integralSingularChains A).X (n + 1) ⟶
    (integralSingularChains X).X n => h b)
      ((integralSingularChainMap (singularSubspaceInclusion A)).comm (n + 1) n)).symm

end DifferentialGeometry.Topology
