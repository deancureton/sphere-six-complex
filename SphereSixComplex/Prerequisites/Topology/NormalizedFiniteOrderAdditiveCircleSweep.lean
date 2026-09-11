module

public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicMappingTorusWangNaturality
public import SphereSixComplex.Prerequisites.Topology.PositiveCircleCross

/-!
# Orbit sweeps for normalized finite-order mapping-torus covers
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweep

open CircleProductIdentityMappingTorus
open FiniteCyclicMappingTorusWangNaturality
open NormalizedAffineMappingTorusCover
open PositiveCircleCross
open StandardTorusHomology

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- Postcomposition by an additive self-homeomorphism on parametrized circle maps. -/
public def loopAction (phi : G ≃ₜ+ G) :
    C(StdTorus 1, G) →ₗ[ℤ] C(StdTorus 1, G) where
  toFun c := (⟨phi, phi.toHomeomorph.continuous⟩ : C(G, G)).comp c
  map_add' c d := by
    ext x
    exact map_add phi (c x) (d x)
  map_smul' n c := by
    ext x
    exact map_zsmul phi.toAddEquiv n (c x)

/-- Parametrized circle maps fixed pointwise after postcomposition by `phi`. -/
public abbrev fixedLoops (phi : G ≃ₜ+ G) :=
  LinearMap.ker (loopAction phi - LinearMap.id)





end SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweep

end

end
