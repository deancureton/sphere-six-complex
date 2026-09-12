module
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberSpecializationGeometricReduction

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus TorusFamily GlobalTorusFamily EllipticFamilySpecialization
open CuspPuncturedCollarBridge CuspRadialClutchingConstruction CuspPeriodExpansion

public def cuspFiniteFiberPairIndex : Fin 4 → Fin 6 := ![0,2,3,1]

public theorem cuspFiniteFiberPairIndex_representative (j : Fin 4) :
    ActualCuspRadialClutchingData.degreeTwoCoinvariantRepresentative (Pi.single j 1) =
      Pi.single (cuspFiniteFiberPairIndex j) 1 := by
  ext i
  fin_cases j <;> fin_cases i <;> rfl

public def cuspFiniteFiberCoordinateTorus (A : AnalyticData) (j : Fin 4) :
    C(StdTorus 2, AdditiveTorus (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)).1) :=
  ((additiveTorusStdHomeomorph _ (fullRankDomain (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))).symm : C(_, _)).comp
    (standardFourTorusCoordinateTwoTorus (cuspFiniteFiberPairIndex j))

public theorem cuspFiniteFiberCoordinateTorus_generator (A : AnalyticData) (j : Fin 4) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    integralSingularHomologyMap 2 (A.cuspFiniteFiberCoordinateTorus j)
      standardTwoTorusHomologyGenerator = G.degreeTwoFiberGenerator j := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  apply G.monodromyCoordinates.degreeTwo.injective
  rw [ActualCuspRadialClutchingData.degreeTwoFiberGenerator,
    G.monodromyCoordinates.degreeTwo.apply_symm_apply,
    cuspFiniteFiberPairIndex_representative]
  change stdTorusFourHomologyTwo (integralSingularHomologyMap 2
    (additiveTorusStdHomeomorph _ (fullRankDomain (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness))) : C(_, _))
    (integralSingularHomologyMap 2 (A.cuspFiniteFiberCoordinateTorus j)
      standardTwoTorusHomologyGenerator)) = _
  rw [integralSingularHomologyMap_comp_wang]
  have he : (additiveTorusStdHomeomorph _ (fullRankDomain (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness))) : C(_, _)).comp
      (A.cuspFiniteFiberCoordinateTorus j) =
      standardFourTorusCoordinateTwoTorus (cuspFiniteFiberPairIndex j) := by
    ext1 z
    exact (additiveTorusStdHomeomorph _ (fullRankDomain (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))).apply_symm_apply _
  rw [he]
  exact standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass _

public theorem cuspFiniteFiberCoordinateTorus_real (A : AnalyticData) (j : Fin 4)
    (t s : ℝ) :
    A.cuspFiniteFiberCoordinateTorus j ![(t : UnitAddCircle),(s : UnitAddCircle)] =
      additiveTorusProjection (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1
        (t • periodVector (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)).1 (Pi.single (standardPeriodPairFirst (cuspFiniteFiberPairIndex j)) 1) +
         s • periodVector (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)).1 (Pi.single (standardPeriodPairSecond (cuspFiniteFiberPairIndex j)) 1)) := by
  apply (additiveTorusStdHomeomorph _ (fullRankDomain
    (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))).injective
  change (additiveTorusStdHomeomorph _ (fullRankDomain _))
    ((additiveTorusStdHomeomorph _ (fullRankDomain _)).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  change _ = periodCoordMap _ _ _
  ext i
  simp only [periodCoordMap, map_add, map_smul, realEquiv_symm_periodVector]
  fin_cases j <;> fin_cases i <;>
    simp [standardFourTorusCoordinateTwoTorus, cuspFiniteFiberPairIndex,
      standardPeriodPairFirst, standardPeriodPairSecond, integerToReal]

public def cuspFiniteFiberTorusToFilling (A : AnalyticData) (j : Fin 4) :
    C(StdTorus 2,ActualLocalCuspFilling A.starCuspWitness) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  exact G.markedFiberToCuspFilling.comp (A.cuspFiniteFiberCoordinateTorus j)

public theorem cuspFiniteFiberTorusToFilling_homology (A : AnalyticData) (j : Fin 4) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    let _ := G.fiberTopology
    integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling j)
      standardTwoTorusHomologyGenerator =
      integralSingularHomologyMap 2 G.markedFiberToCuspFilling (G.degreeTwoFiberGenerator j) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  change integralSingularHomologyMap 2
    (G.markedFiberToCuspFilling.comp (A.cuspFiniteFiberCoordinateTorus j)) _ = _
  erw [← integralSingularHomologyMap_comp_wang]
  exact congrArg (integralSingularHomologyMap 2 G.markedFiberToCuspFilling)
    (A.cuspFiniteFiberCoordinateTorus_generator j)

public theorem cuspFiniteFiberTorusToFilling_real (A : AnalyticData) (j : Fin 4)
    (t s : ℝ) :
    let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
    A.cuspFiniteFiberTorusToFilling j ![(t : UnitAddCircle),(s : UnitAddCircle)] =
      puncturedLocalCuspToFilling A.starCuspWitness
        (actualCuspCollarPeriodPoint A.starCuspWitness G.markingParameter_mem
          (t • periodVector (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1
              (Pi.single (standardPeriodPairFirst (cuspFiniteFiberPairIndex j)) 1) +
           s • periodVector (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1
              (Pi.single (standardPeriodPairSecond (cuspFiniteFiberPairIndex j)) 1))) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  apply G.markedFiberToCuspFilling_eq_actualCuspCollarPeriodPoint
  exact A.cuspFiniteFiberCoordinateTorus_real j t s

end SphereSixComplex.Geometry.AnalyticData
