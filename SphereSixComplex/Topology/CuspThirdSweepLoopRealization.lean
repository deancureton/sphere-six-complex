module
public import SphereSixComplex.Topology.CuspCoordinateCircleTransport
public import SphereSixComplex.Topology.CircleSweepWhiskerHomotopy

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
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open CircleProductIdentityMappingTorus

public def actualCuspThirdSweepCentral (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.CentralFamily) :=
  ⟨fun p ↦ A.starToCentral 0 (actualCuspThirdSweep A p),
    (A.starToCentral_isOpenEmbedding 0).continuous.comp (actualCuspThirdSweep A).continuous⟩

public theorem actualCuspThirdSweepCentral_loop_realization (A : PaperAnalyticData) :
    identityMappingTorusMapOfLoop A.actualCuspThirdPeriodLoop =
      A.actualCuspThirdSweepCentral.comp
        ((circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).symm :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1)) := by
  ext z
  induction z using Quotient.inductionOn with
  | _ z =>
    obtain ⟨u, t, x⟩ := z
    cases u
    change A.actualCuspThirdPeriodLoop t x =
      A.actualCuspThirdSweepCentral (circleProductIdentityMappingTorusHomeomorph.symm
        (torusPt (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) () t x))
    rw [circleProductIdentityMappingTorusHomeomorph_symm_interval]
    exact A.actualCuspThirdPeriodFamily_eq_sweep t x

public theorem actualCuspThirdSweepCentral_homology_realization (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    integralSingularHomologyMap 2 A.actualCuspThirdSweepCentral x =
      integralSingularHomologyMap 2
        (identityMappingTorusMapOfLoop A.actualCuspThirdPeriodLoop)
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
          C(UnitAddCircle × StdTorus 1, CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) x) := by
  rw [integralSingularHomologyMap_comp_wang, actualCuspThirdSweepCentral_loop_realization]
  have h : (A.actualCuspThirdSweepCentral.comp
      ((circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).symm :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1))).comp
        (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
          C(UnitAddCircle × StdTorus 1, CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) =
      A.actualCuspThirdSweepCentral := by
    ext z
    exact congrArg A.actualCuspThirdSweepCentral
      (circleProductIdentityMappingTorusHomeomorph.symm_apply_apply z)
  rw [h]

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
