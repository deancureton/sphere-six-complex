module

public import
  SphereSixComplex.Topology.PaperSectionSevenCuspActualCoordinateScalarsFromExistingGeometry

/-!
# Full cusp marked-coordinate package from existing geometry

The topological cusp--band square supplies the two degree-one fibre values and the four
degree-two fibre-coinvariant values.  The genuinely complementary geometry is the meridian
projection and the normalized first invariant-suspension prism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The canonical prism geometry obtained from the proved fibre-coordinate values. -/
public noncomputable def cuspPrismGeometryOfExistingFiberValues
    (R : A.SectionSevenAffineRadialCompletionInput)
    (G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment)
    (hTop : R.twoDiscCover.CanonicalCuspFiberBandTopologicalCompatibility)
    (M : R.twoDiscCover.CuspEllipticMappingTorusMeridianProjectionComparison
      R.homologyAlignment) :
    R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment G₀ := by
  apply cuspEllipticMappingTorusPrismGeometricData_of_fiberCoinvariantValues M
  intro i hi4 hi5
  fin_cases i
  · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
    simpa [actualCuspEllipticDegreeTwoFiberRawCoordinate] using congrFun
      (affineActualCuspDegreeTwoFiberBasis_scalarValues R
        (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment G₀) hTop) 0
  · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
    simpa [actualCuspEllipticDegreeTwoFiberRawCoordinate] using congrFun
      (affineActualCuspDegreeTwoFiberBasis_scalarValues R
        (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment G₀) hTop) 1
  · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
    simpa [actualCuspEllipticDegreeTwoFiberRawCoordinate] using congrFun
      (affineActualCuspDegreeTwoFiberBasis_scalarValues R
        (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment G₀) hTop) 2
  · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
    simpa [actualCuspEllipticDegreeTwoFiberRawCoordinate] using congrFun
      (affineActualCuspDegreeTwoFiberBasis_scalarValues R
        (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment G₀) hTop) 3
  · exact (hi4 rfl).elim
  · exact (hi5 rfl).elim

/-- The complete marked-coordinate calculation follows from the topological cusp--band square,
the meridian projection, and normalization of the first invariant-suspension prism. -/
public theorem actualCuspFiberEllipticMarkedCoordinateCalculation_of_existingGeometry
    (R : A.SectionSevenAffineRadialCompletionInput)
    (G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment)
    (hTop : R.twoDiscCover.CanonicalCuspFiberBandTopologicalCompatibility)
    (M : R.twoDiscCover.CuspEllipticMappingTorusMeridianProjectionComparison
      R.homologyAlignment)
    (I : R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation
      (cuspPrismGeometryOfExistingFiberValues R G₀ hTop M)) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R G₀ := by
  let C := cuspPrismGeometryOfExistingFiberValues R G₀ hTop M
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hTwo :
      (R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          G₀).comp
          (integralSingularHomologyMap 2
            R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
        actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv
          G.geometricWangSections.circleMappingTorusHTwoAddEquiv := by
    rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic C.modelHomotopy]
    exact (C.suspensionPrismComparison (C.normalizedIndexFourPrismCalculation I)).degreeTwoFiber
  refine { degreeOne := ?_, degreeTwoFiberCoinvariant := ?_, degreeTwoIndexFour := ?_ }
  · intro i
    fin_cases i
    · simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeOneCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeOneRawCoordinate] using congrFun
        (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 0
    · simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeOneCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeOneRawCoordinate] using congrFun
        (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 1
    · have h := DFunLike.congr_fun M.degreeOne
          (A.actualCuspRadialClutchingData.geometricWangSections
            |>.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (2 : Fin 3) 1))
      simpa [actualCuspEllipticDegreeOneCoordinateAfterAddEquiv,
        AddMonoidHom.comp_apply,
        A.actualCuspRadialClutchingData.geometricWangSections
          |>.circleMappingTorusHOneAddEquiv.apply_symm_apply] using h
  · intro i _hi4 _hi5
    rw [← cuspMappingTorusToEllipticInteriorMap_basis]
    have h := DFunLike.congr_fun hTwo
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1))
    simpa [actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv,
      AddMonoidHom.comp_apply] using h
  · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
    have h := DFunLike.congr_fun hTwo
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
        (Pi.single (4 : Fin 6) 1))
    simpa [actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv,
      actualCuspEllipticDegreeTwoFiberRawCoordinate, AddMonoidHom.comp_apply] using h

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
