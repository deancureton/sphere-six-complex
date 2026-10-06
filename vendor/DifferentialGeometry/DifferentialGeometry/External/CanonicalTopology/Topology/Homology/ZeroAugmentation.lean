module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TotallyDisconnectedZero
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ConnectedZeroHomology
public import Mathlib.LinearAlgebra.Finsupp.Pi

@[expose] public section

/-! # The normalized augmentation of actual integral H0 -/

noncomputable section

open CategoryTheory ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- Original H0 of the one-point space, normalized by its actual vertex. -/
def integralPointZeroEquiv :
    integralSingularHomology 0 PUnit.{u + 1} ≃ₗ[ℤ] ℤ :=
  integralTotallyDisconnectedZeroEquiv.trans (Finsupp.uniqueLinearEquiv ℤ ℤ PUnit.unit)

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual H0 map to a point, in normalized integral coordinates. -/
def integralZeroAugmentation : integralSingularHomology 0 X →ₗ[ℤ] ℤ :=
  integralPointZeroEquiv.toLinearMap.comp
    (integralSingularHomologyMap 0 (ContinuousMap.const X PUnit.unit))

/-- Every original vertex class has augmentation one. -/
theorem integralZeroAugmentation_vertex (x : X) :
    integralZeroAugmentation (integralZeroChainClass (integralVertexChain x)) = 1 := by
  change integralPointZeroEquiv (integralSingularHomologyMap 0 (.const X PUnit.unit)
    (integralZeroChainClass (integralVertexChain x))) = _
  rw [integralZeroChainClass_map, integralVertexChain_map]
  change Finsupp.uniqueLinearEquiv ℤ ℤ PUnit.unit
    (integralTotallyDisconnectedZeroEquiv (integralZeroChainClass
      (integralVertexChain PUnit.unit))) = _
  rw [integralTotallyDisconnectedZeroEquiv_vertex]
  simp [Finsupp.uniqueLinearEquiv]

/-- The augmentation commutes with every original continuous map. -/
theorem integralZeroAugmentation_natural (f : C(X, Y)) :
    integralZeroAugmentation.comp (integralSingularHomologyMap 0 f) =
      integralZeroAugmentation := by
  unfold integralZeroAugmentation
  rw [LinearMap.comp_assoc, ← integralSingularHomologyMap_comp]
  rfl

/-- On a path-connected space the SAME normalized augmentation is an
isomorphism, as proved using actual paths and the actual map to a point. -/
def integralConnectedZeroAugmentationEquiv [PathConnectedSpace X] :
    integralSingularHomology 0 X ≃ₗ[ℤ] ℤ :=
  (integralSingularHomologyZeroMapEquiv (ContinuousMap.const X PUnit.unit)).trans
    integralPointZeroEquiv

/-- This equivalence uses the SAME augmentation, not an arbitrary H0 basis. -/
theorem integralConnectedZeroAugmentationEquiv_toLinearMap [PathConnectedSpace X] :
    (integralConnectedZeroAugmentationEquiv (X := X)).toLinearMap = integralZeroAugmentation := rfl

end DifferentialGeometry.Topology
