module
public import SphereSixComplex.Topology.CuspFourthSweepToricLift
public import SphereSixComplex.Topology.CuspFourthSweepFiberParity

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology CuspPuncturedCollarBridge
open SectionSevenEllipticTwoDiscCoverData

public theorem actualCuspFourthSweepClass_raw_fiber_zero (A : PaperAnalyticData) (i : Fin 4) :
    A.actualCuspRawHomologyTwoEquiv (actualCuspFourthSweepClass A) (Fin.castAdd 2 i) = 0 := by
  have h := EstablishedStandardA2CuspSpecialization.degreeTwo A (actualCuspFourthSweepClass A)
  have hz := actualCuspFourthSweep_filling_homology_zero A
    PositiveCircleCross.positiveCircleProductGenerator
  change integralSingularHomologyMap 2 _ (actualCuspFourthSweepClass A) = 0 at hz
  have he := congrArg (actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
    A.cuspCentralFiberRetractionData) hz
  exact (congrFun h i).symm.trans ((congrFun he i).trans
    (congrFun (map_zero (actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
      A.cuspCentralFiberRetractionData)) i))

public theorem actualCuspFourthSweepClass_eq_rawFive (A : PaperAnalyticData) :
    actualCuspFourthSweepClass A =
      A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology

  apply A.actualCuspRawHomologyTwoEquiv.injective
  rw [A.actualCuspRawHomologyTwoEquiv.apply_symm_apply]
  have hw := actualCuspWangBoundaryHom_rawCoordinates A (actualCuspFourthSweepClass A)
  have hs := actualCuspFourthSweep_wang A
  dsimp only at hw
  change A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
    (actualCuspWangBoundaryHom A (actualCuspFourthSweepClass A)) = Pi.single (3 : Fin 4) 1 at hs
  rw [hs] at hw
  ext i
  fin_cases i
  · exact actualCuspFourthSweepClass_raw_fiber_zero A 0
  · exact actualCuspFourthSweepClass_raw_fiber_zero A 1
  · exact actualCuspFourthSweepClass_raw_fiber_zero A 2
  · exact actualCuspFourthSweepClass_raw_fiber_zero A 3
  · exact (congrFun hw (2 : Fin 4)).symm
  · exact (congrFun hw (3 : Fin 4)).symm

end SphereSixComplex.Geometry.PaperAnalyticData

