module
public import SphereSixComplex.Paper.Topology.CuspCoordinateCircleTransport
public import SphereSixComplex.Prerequisites.Topology.CircleSweepWhiskerHomotopy

@[expose] public section
noncomputable section
open AlgebraicTopology SphereSixComplex.CyclicAngularFundamentalDomain
open scoped ContinuousMap
namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus

public theorem circleProductIdentityMappingTorusHomeomorph_symm_interval
    {X : Type} [TopologicalSpace X] (t : unitInterval) (x : X) :
    circleProductIdentityMappingTorusHomeomorph.symm
      (torusPt (fun _ : Unit ↦ Homeomorph.refl X) () t x) =
      (((t : ℝ) : UnitAddCircle), x) := by
  change circleProductIdentityMappingTorusHomeomorph.symm
    (circleMappingTorusCylinderProjection (Homeomorph.refl X) (t, x)) = _
  rw [← circleProductIdentityMappingTorusHomeomorph_interval, Homeomorph.symm_apply_apply]

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus
end
end
