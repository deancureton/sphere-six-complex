module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractiblePairOne

@[expose] public section

/-! # The exact degree-one homology kernel for the original contractible cover -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Retain the original kernel's integer action for the actual H0 inclusion map. -/
instance integralRelativeZeroKernelModule (A : Set X) :
    Module ℤ (LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A))) :=
  (LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A))).module

/-- For a contractible original ambient space, the SAME connecting map
identifies relative H1 with the actual kernel of the ORIGINAL H0 inclusion map. -/
def integralRelativeConnectingZeroKernelEquiv [ContractibleSpace X] (A : Set X) :
    integralRelativeHomology 1 A ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A)) :=
  (LinearEquiv.ofInjective (integralRelativeConnecting 0 A)
    (integralRelativeConnecting_zero_injective A)).trans
      (LinearEquiv.ofEq _ _ ((LinearMap.exact_iff.mp (integralRelative_exact_subspace 0 A)).symm))

/-- A path-connected space covered by two actual contractible open sets
has ORIGINAL H1 identified with the actual kernel of the inclusion on H0
of the SAME intersection. This completes the low-degree cover computation. -/
def integralHomologyOneContractibleCoverEquiv [PathConnectedSpace X] (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    integralSingularHomology 1 X ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion (subspaceIntersection A B))) :=
  ((integralAbsoluteToRelativeOneIsoOfContractible A).toLinearEquiv.trans
    (integralRelativeOpenExcisionIso 1 A B hA hB hcover).symm.toLinearEquiv).trans
      (integralRelativeConnectingZeroKernelEquiv (subspaceIntersection A B))

end DifferentialGeometry.Topology
