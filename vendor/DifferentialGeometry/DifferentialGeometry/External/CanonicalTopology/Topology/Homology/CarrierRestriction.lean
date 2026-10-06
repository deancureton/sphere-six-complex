module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainsIn
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionNaturality

@[expose] public section

/-! # Exact restriction of original singular chains to their carrier -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Retain the original carrier submodule's integer scalar action. -/
instance integralSingularChainsInModule (n : ℕ) (A : Set X) :
    Module ℤ (integralSingularChainsIn n A) := (integralSingularChainsIn n A).module

/-- Inclusion is injective in each original chain degree. -/
theorem integralSingularChainInclusion_injective (n : ℕ) (A : Set X) :
    Function.Injective ((integralSingularChainMap (singularSubspaceInclusion A)).f n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- Chains on the original subspace are exactly the original chains carried
by it, with the same coefficients and boundary parametrizations. -/
def integralSingularChainCarrierEquiv (n : ℕ) (A : Set X) :
    (integralSingularChains A).X n ≃ₗ[ℤ] integralSingularChainsIn n A :=
  (LinearEquiv.ofInjective ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
    (integralSingularChainInclusion_injective n A)).trans
      (LinearEquiv.ofEq _ _ (integralSingularChainsIn_eq_range n A).symm)

/-- This equivalence has the original inclusion as its underlying map. -/
theorem integralSingularChainCarrierEquiv_coe (n : ℕ) (A : Set X)
    (c : (integralSingularChains A).X n) :
    (integralSingularChainCarrierEquiv n A c).val =
      (integralSingularChainMap (singularSubspaceInclusion A)).f n c := rfl

/-- Exact linear restriction to the actual carrier, inverse to inclusion. -/
def integralSingularChainRestriction (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A →ₗ[ℤ] (integralSingularChains A).X n :=
  (integralSingularChainCarrierEquiv n A).symm.toLinearMap

/-- Including a restricted chain recovers that SAME original chain. -/
theorem integralSingularChainRestriction_inclusion (n : ℕ) (A : Set X)
    (c : integralSingularChainsIn n A) :
    (integralSingularChainMap (singularSubspaceInclusion A)).f n
      (integralSingularChainRestriction n A c) = c.val :=
  congrArg Subtype.val ((integralSingularChainCarrierEquiv n A).apply_symm_apply c)

/-- Restriction commutes with the actual boundary, through the proved
carrier preservation of that same boundary. -/
theorem integralSingularChainRestriction_boundary (n : ℕ) (A : Set X)
    (c : integralSingularChainsIn (n + 1) A) :
    integralSingularChainRestriction n A
      ⟨(integralSingularChains X).d (n + 1) n c.val, integralSingularChainsIn_boundary n A c.property⟩ =
      (integralSingularChains A).d (n + 1) n (integralSingularChainRestriction (n + 1) A c) := by
  apply integralSingularChainInclusion_injective n A
  rw [integralSingularChainRestriction_inclusion, integralSingularChainMap_boundary,
    integralSingularChainRestriction_inclusion]

end DifferentialGeometry.Topology
