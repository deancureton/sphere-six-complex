module
public import SphereSixComplex.Paper.Topology.CuspCoordinateCircleTransport
public import SphereSixComplex.Prerequisites.Topology.CircleSweepWhiskerHomotopy

@[expose] public section
noncomputable section
open AlgebraicTopology SphereSixComplex.CyclicAngularFundamentalDomain
open scoped ContinuousMap
namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus

public theorem circleProductIdentityMappingTorusHomeomorph_interval
    {X : Type} [TopologicalSpace X] (t : unitInterval) (x : X) :
    circleProductIdentityMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), x) =
      torusPt (fun _ : Unit ↦ Homeomorph.refl X) () t x := by
  change realMappingTorusHomeomorph (Homeomorph.refl X)
    (circleProductRealMappingTorusHomeomorph (realToCircleProduct ((t : ℝ), x))) = _
  rw [circleProductRealMappingTorusHomeomorph_real]
  let D := realMappingTorusClutchingData (Homeomorph.refl X)
  change D.totalHomeomorphCircleMappingTorus (D.projection (t, x)) = _
  apply D.totalHomeomorphCircleMappingTorus.symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

public theorem circleProductIdentityMappingTorusHomeomorph_symm_interval
    {X : Type} [TopologicalSpace X] (t : unitInterval) (x : X) :
    circleProductIdentityMappingTorusHomeomorph.symm
      (torusPt (fun _ : Unit ↦ Homeomorph.refl X) () t x) =
      (((t : ℝ) : UnitAddCircle), x) := by
  rw [← circleProductIdentityMappingTorusHomeomorph_interval, Homeomorph.symm_apply_apply]

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus
end
end
