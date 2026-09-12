module
public import SphereSixComplex.Paper.Topology.CuspMixedPhaseTorus
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberCoordinateCircles
public import SphereSixComplex.Paper.Topology.CuspPeriodCellularHomology
import all SphereSixComplex.Paper.Periods.Matrix

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus GlobalTorusFamily
open CuspPuncturedCollarBridge CuspRadialClutchingConstruction CuspPeriodExpansion
open PositiveCircleCross CircleProductIdentityMappingTorus StandardCircleHomologyLiftDegree

public def cuspMixedTorusIndex : Fin 3 → Fin 4 := ![1,2,3]
public def cuspMixedTorusPeriod : Fin 3 → Fin 2 := ![0,1,0]
public def cuspMixedTorusPhase : Fin 3 → Fin 2 := ![1,0,0]

public theorem cuspMixedTorus_phasePoint (A : AnalyticData) (j : Fin 3)
    (t s : UnitAddCircle) :
    cuspFillingPeriodCircle A.starCuspWitness (cuspMixedTorusPhase j)
      (s,A.cuspFiniteFiberCircleToFilling (cuspMixedTorusPeriod j) (fun _ ↦ t)) =
      A.cuspFiniteFiberTorusToFilling (cuspMixedTorusIndex j) ![t,s] := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective s
  rw [cuspFiniteFiberCircleToFilling_real, cuspFillingPeriodCircle_periodPoint,
    cuspFiniteFiberTorusToFilling_real]
  congr 2
  fin_cases j <;>
    change _ + Pi.single _ (s : ℂ) = _ + s • periodVector _ _
  all_goals
    congr 1
    ext i
    fin_cases i <;> simp [periodVector, periodMatrix, Matrix.vecHead, Matrix.vecTail,
      cuspMixedTorusPhase, cuspMixedTorusIndex, cuspFiniteFiberPairIndex,
      standardPeriodPairSecond]

public theorem cuspMixedTorus_phaseSweep (A : AnalyticData) (j : Fin 3) :
    A.cuspFillingPhaseSweep (cuspMixedTorusPhase j)
      (integralSingularHomologyMap 1
        (A.cuspFiniteFiberCircleToFilling (cuspMixedTorusPeriod j))
        standardCircleHomologyGenerator) =
      -integralSingularHomologyMap 2
        (A.cuspFiniteFiberTorusToFilling (cuspMixedTorusIndex j))
        standardTwoTorusHomologyGenerator := by
  change integralSingularHomologyMap 2
    (cuspFillingPeriodCircle A.starCuspWitness (cuspMixedTorusPhase j))
    (normalizedCircleCross 1 _) = _
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 _
    (integralSingularHomologyMap 2
      (circleProductMap (A.cuspFiniteFiberCircleToFilling (cuspMixedTorusPeriod j)))
      positiveCircleProductGenerator) = _
  rw [integralSingularHomologyMap_comp_wang]
  have he : (cuspFillingPeriodCircle A.starCuspWitness (cuspMixedTorusPhase j)).comp
      (circleProductMap (A.cuspFiniteFiberCircleToFilling (cuspMixedTorusPeriod j))) =
      (A.cuspFiniteFiberTorusToFilling (cuspMixedTorusIndex j)).comp
        ((circleProdStandardCircleHomeomorph : C(_, _)).comp positiveCircleProductSwap) := by
    ext1 p
    have hp : p.2 = (fun _ ↦ p.2 0) := by ext i; fin_cases i; rfl
    change cuspFillingPeriodCircle _ _
      (p.1,A.cuspFiniteFiberCircleToFilling _ p.2) = _
    rw [hp, cuspMixedTorus_phasePoint]
    rfl
  rw [he, ← integralSingularHomologyMap_comp_wang,
    ← integralSingularHomologyMap_comp_wang, positiveCircleProductSwap_generator,
    map_neg, map_neg]
  congr 2
  exact (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).apply_symm_apply _

local instance (A : AnalyticData) :
    T2Space (ActualLocalCuspCentralOrbitQuotient A.starCuspWitness) := by
  let _ := actualLocalCuspFilling_t2 A.starCuspWitness
  exact (actualLocalCuspCentralOrbitMap_isEmbedding A.starCuspWitness).t2Space

public theorem cuspFiniteFiberCircleToFilling_cellular (A : AnalyticData) (j : Fin 2) :
    integralSingularHomologyMap 1 (A.cuspFiniteFiberCircleToFilling j)
      standardCircleHomologyGenerator =
      (-(Pi.single j 1 : Fin 2 → ℤ) 0 + (Pi.single j 1 : Fin 2 → ℤ) 1) •
        loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 0 2) +
      (-(Pi.single j 1 : Fin 2 → ℤ) 1) •
        loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 1 2) := by
  rw [cuspFiniteFiberCircleToFilling_loop]
  exact localCuspPeriodLoop_cellularHomology A.starCuspWitness _ _ _ _

public theorem cuspMixedTorus_cellularSweeps (A : AnalyticData) (j : Fin 3) :
    integralSingularHomologyMap 2
      (A.cuspFiniteFiberTorusToFilling (cuspMixedTorusIndex j))
      standardTwoTorusHomologyGenerator =
      -((-(Pi.single (cuspMixedTorusPeriod j) 1 : Fin 2 → ℤ) 0 +
            (Pi.single (cuspMixedTorusPeriod j) 1 : Fin 2 → ℤ) 1) •
          A.cuspFillingPhaseSweep (cuspMixedTorusPhase j)
            (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 0 2)) +
        (-(Pi.single (cuspMixedTorusPeriod j) 1 : Fin 2 → ℤ) 1) •
          A.cuspFillingPhaseSweep (cuspMixedTorusPhase j)
            (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 1 2))) := by
  calc
    _ = -A.cuspFillingPhaseSweep (cuspMixedTorusPhase j)
        (integralSingularHomologyMap 1
          (A.cuspFiniteFiberCircleToFilling (cuspMixedTorusPeriod j))
          standardCircleHomologyGenerator) := by
      rw [cuspMixedTorus_phaseSweep, neg_neg]
    _ = _ := by rw [cuspFiniteFiberCircleToFilling_cellular, map_add, map_zsmul, map_zsmul]

public theorem cuspMixedFourthTorus_cellularSweep (A : AnalyticData) :
    integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling 1)
      standardTwoTorusHomologyGenerator =
      A.cuspFillingPhaseSweep 1
        (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 0 2)) := by
  simpa [cuspMixedTorusIndex, cuspMixedTorusPeriod, cuspMixedTorusPhase] using
    A.cuspMixedTorus_cellularSweeps 0

public theorem cuspMixedThirdSecondTorus_cellularSweeps (A : AnalyticData) :
    integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling 2)
      standardTwoTorusHomologyGenerator =
      -A.cuspFillingPhaseSweep 0
          (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 0 2)) +
        A.cuspFillingPhaseSweep 0
          (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 1 2)) := by
  rw [add_comm]
  simpa [cuspMixedTorusIndex, cuspMixedTorusPeriod, cuspMixedTorusPhase] using
    A.cuspMixedTorus_cellularSweeps 1

public theorem cuspMixedThirdFirstTorus_cellularSweep (A : AnalyticData) :
    integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling 3)
      standardTwoTorusHomologyGenerator =
      A.cuspFillingPhaseSweep 0
        (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness 0 2)) := by
  simpa [cuspMixedTorusIndex, cuspMixedTorusPeriod, cuspMixedTorusPhase] using
    A.cuspMixedTorus_cellularSweeps 2

end SphereSixComplex.Geometry.AnalyticData
