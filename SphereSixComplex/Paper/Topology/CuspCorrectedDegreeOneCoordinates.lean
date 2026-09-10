module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspDegreeOneIndexTwoProof

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology
open EllipticInteriorMarkedCycleData EllipticTwoDiscCoverData
open EstablishedSectionSevenCuspTopology EllipticTwoDiscHomologyCoordinates

public theorem cuspDegreeOneMappingTorusCoordinates_of_fullIterate
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput)
    (h : ActualCuspDegreeOneIndexTwoFullIterateRelation R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
      (integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply addMonoidHom_ext_of_equiv_pi_single_one G.geometricWangSections.circleMappingTorusHOneAddEquiv
  intro i
  change _ = cuspEllipticDegreeOneRawCoordinate
    (G.geometricWangSections.circleMappingTorusHOneAddEquiv
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)))
  rw [AddEquiv.apply_symm_apply]
  let hTop := canonicalCuspFiberBandTopologicalCompatibility R
  fin_cases i
  · simpa [ellipticInteriorDegreeOneCoordinateHom, coordinateAfterAddEquiv_apply,
      cuspEllipticDegreeOneRawCoordinate] using congrFun
        (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 0
  · simpa [ellipticInteriorDegreeOneCoordinateHom, coordinateAfterAddEquiv_apply,
      cuspEllipticDegreeOneRawCoordinate] using congrFun
        (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 1
  · simpa [cuspEllipticDegreeOneRawCoordinate] using
      (actualCuspDegreeOneIndexTwo_iff_fullIterateRelation R).mpr h

public theorem cuspDegreeOneUnionCoordinates_of_fullIterate
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput)
    (h : ActualCuspDegreeOneIndexTwoFullIterateRelation R)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
      (cuspToEllipticUnionHomology R.twoDiscCover 1 x) 0 =
      cuspEllipticDegreeOneRawCoordinate (A.cuspRawHomologyOneEquiv x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hx := DFunLike.congr_fun (cuspDegreeOneMappingTorusCoordinates_of_fullIterate R h)
    (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun x)
  change R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment
      (integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun x)) =
    cuspEllipticDegreeOneRawCoordinate
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun x)) at hx
  rw [← R.twoDiscCover.cuspToEllipticInteriorMap_homology_mappingTorusModel 1 x,
    R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap,
    ← actualCuspRawHomologyOneEquiv_apply_mappingTorus A x] at hx
  exact hx

end SphereSixComplex.Geometry.PaperAnalyticData
end
