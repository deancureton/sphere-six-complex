module
public import SphereSixComplex.Paper.Topology.CuspThirdCircle
public import SphereSixComplex.Paper.Topology.CuspFixedCircleSweep

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open CuspRadialClutchingConstruction CuspPuncturedCollarBridge
open SectionSevenEllipticTwoDiscCoverData

public def cuspThirdSweep (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) :=
  cuspFixedCircleSweep A (cuspThirdFixedCircle (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness)))

public theorem cuspThirdSweep_wang (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.monodromyCoordinates.degreeOne
      (actualCuspWangBoundaryHom A
        (integralSingularHomologyMap 2 (cuspThirdSweep A)
          PositiveCircleCross.positiveCircleProductGenerator)) = Pi.single 2 1 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  change (cuspMonodromyCoordinates _).degreeOne
    (actualCuspWangBoundaryHom A
      (integralSingularHomologyMap 2 (cuspFixedCircleSweep A _) _)) = _
  rw [cuspFixedCircleSweep_wang]
  exact cuspCoordinateCircle_homology _ 2

public theorem cuspRawFour_pulled_back_boundary_eq_sweep {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (integralSingularHomologyMap 2 (cuspThirdSweep A)
        PositiveCircleCross.positiveCircleProductGenerator) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply cuspPulledBackBoundary_eq_of_wang_eq R
  apply A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.injective
  rw [actualCuspWangBoundaryHom_rawBasis, AddEquiv.apply_symm_apply,
    cuspThirdSweep_wang]
  ext i
  fin_cases i <;> rfl

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
