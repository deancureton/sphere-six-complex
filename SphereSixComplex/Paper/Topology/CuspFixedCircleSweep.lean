module
public import SphereSixComplex.Paper.Topology.CuspInvariantCoordinateCircle
public import SphereSixComplex.Paper.Topology.CuspWangKernel

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspCollar CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open EllipticTwoDiscCoverData
open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary
open SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open SphereSixComplex.CyclicAngularFundamentalDomain
public def cuspFixedCircleSweep (A : AnalyticData)
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

public theorem cuspFixedCircleSweep_to_mapping_torus (A : AnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) :
    A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun.comp (cuspFixedCircleSweep A c) =
      fixedLoopMappingTorusMap (cuspFiberClutching _)
        c := by
  ext1 p
  change ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness))
    ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness)).symm _)).2 = _
  erw [Homeomorph.apply_symm_apply]
  rfl

public theorem cuspFixedCircleSweep_wang (A : AnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) :
    let _ := A.actualCuspRadialClutchingData.fiberTopology
    actualCuspWangBoundaryHom A
      (integralSingularHomologyMap 2 (cuspFixedCircleSweep A c)
        PositiveCircleCross.positiveCircleProductGenerator) =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  change (circleMappingTorusWangPresentationOfCover _ 1).boundary
    (integralSingularHomologyMap 2 A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 2 (cuspFixedCircleSweep A c) _)) = _
  erw [integralSingularHomologyMap_comp_wang, cuspFixedCircleSweep_to_mapping_torus]
  exact fixedLoopSweepClass_boundary _ c

end SphereSixComplex.Geometry.AnalyticData
end
end
