module
public import SphereSixComplex.Topology.CuspInvariantCoordinateCircle
public import SphereSixComplex.Topology.CuspWangKernel

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open SectionSevenEllipticTwoDiscCoverData
open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary
open SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open SphereSixComplex.CyclicAngularFundamentalDomain
public def actualCuspFixedCircleSweep (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  letI := G.fiberTopology
  let rho : OpenRadialInterval A.starCuspWitness.localWitness.radius :=
    ⟨A.starCuspWitness.localWitness.radius / 2, by
      have := A.starCuspWitness.localWitness.radius_pos
      constructor <;> linarith⟩
  exact (⟨G.totalHomeomorph.symm, G.totalHomeomorph.symm.continuous⟩ : C(_, _)).comp
    ((ContinuousMap.const _ rho).prodMk
      (fixedLoopMappingTorusMap (cuspFiberClutching _)
        c))

public theorem actualCuspFixedCircleSweep_real (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) (r : ℝ)
    (z : StdTorus 1) :
    actualCuspFixedCircleSweep A c ((r : UnitAddCircle), z) =
      actualCuspFullFibreSlice (A := A)
        (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r)
        (by rw [norm_cuspQ_cuspParameterOfPolar _ _ (by
              have := A.starCuspWitness.localWitness.radius_pos; linarith)]
            have := A.starCuspWitness.localWitness.radius_pos; linarith)
        (c.1 z) := by
  have h := circleProductRealMappingTorusHomeomorph_real (X := StdTorus 1) (r, z)
  change circleProductRealMappingTorusHomeomorph ((r : UnitAddCircle), z) = _ at h
  apply (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness)).injective
  change (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _)
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _).symm _) =
    (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _)
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _).symm _)
  erw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (norm_cuspQ_cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r (by
      have := A.starCuspWitness.localWitness.radius_pos; linarith)).symm
  · change realMappingTorusHomeomorph _
      (fixedLoopRealMappingTorusMap _ _
        (circleProductRealMappingTorusHomeomorph ((r : UnitAddCircle), z))) = _
    rw [h, fixedLoopRealMappingTorusMap_mk]
    rfl


public theorem actualCuspFixedCircleSweep_to_mappingTorus (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) :
    A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun.comp (actualCuspFixedCircleSweep A c) =
      fixedLoopMappingTorusMap (cuspFiberClutching _)
        c := by
  ext1 p
  change ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness))
    ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness)).symm _)).2 = _
  erw [Homeomorph.apply_symm_apply]
  rfl


public theorem actualCuspFixedCircleSweep_wang (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) :
    let _ := A.actualCuspRadialClutchingData.fiberTopology
    actualCuspWangBoundaryHom A
      (integralSingularHomologyMap 2 (actualCuspFixedCircleSweep A c)
        PositiveCircleCross.positiveCircleProductGenerator) =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  change (circleMappingTorusWangPresentationOfCover _ 1).boundary
    (integralSingularHomologyMap 2 A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 2 (actualCuspFixedCircleSweep A c) _)) = _
  erw [integralSingularHomologyMap_comp_wang, actualCuspFixedCircleSweep_to_mappingTorus]
  exact fixedLoopSweepClass_boundary _ c

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
