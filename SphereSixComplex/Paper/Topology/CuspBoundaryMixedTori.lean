module
public import SphereSixComplex.Paper.Topology.CuspMixedPhaseTorus
public import SphereSixComplex.Paper.Topology.CuspPhaseCentralCompatibility
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberCoordinateCircles
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryPeriodLoops
import all SphereSixComplex.Paper.Periods.Matrix

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus GlobalTorusFamily
open CuspCollar CuspRadialClutchingConstruction CuspPeriodExpansion
open PositiveCircleCross CircleProductIdentityMappingTorus StandardCircleHomologyLiftDegree

open InfiniteA2Toric.Construction
namespace BoundaryMixedTori

public def index : Fin 3 → Fin 4 := ![1,2,3]
public def period : Fin 3 → Fin 2 := ![0,1,0]
public def phase : Fin 3 → Fin 2 := ![1,0,0]

public theorem phasePoint (A : AnalyticData) (j : Fin 3)
    (t s : UnitAddCircle) :
    cuspFillingPeriodCircle A.starCuspWitness (phase j)
      (s,A.cuspFiniteFiberCircleToFilling (period j) (fun _ ↦ t)) =
      A.cuspFiniteFiberTorusToFilling (index j) ![t,s] := by
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
      phase, index, cuspFiniteFiberPairIndex,
      standardPeriodPairSecond]

public theorem phaseSweep (A : AnalyticData) (j : Fin 3) :
    A.cuspFillingPhaseSweep (phase j)
      (integralSingularHomologyMap 1
        (A.cuspFiniteFiberCircleToFilling (period j))
        standardCircleHomologyGenerator) =
      -integralSingularHomologyMap 2
        (A.cuspFiniteFiberTorusToFilling (index j))
        standardTwoTorusHomologyGenerator := by
  change integralSingularHomologyMap 2
    (cuspFillingPeriodCircle A.starCuspWitness (phase j))
    (normalizedCircleCross 1 _) = _
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 _
    (integralSingularHomologyMap 2
      (circleProductMap (A.cuspFiniteFiberCircleToFilling (period j)))
      positiveCircleProductGenerator) = _
  rw [integralSingularHomologyMap_comp_wang]
  have he : (cuspFillingPeriodCircle A.starCuspWitness (phase j)).comp
      (circleProductMap (A.cuspFiniteFiberCircleToFilling (period j))) =
      (A.cuspFiniteFiberTorusToFilling (index j)).comp
        ((circleProdStandardCircleHomeomorph : C(_, _)).comp positiveCircleProductSwap) := by
    ext1 p
    have hp : p.2 = (fun _ ↦ p.2 0) := by ext i; fin_cases i; rfl
    change cuspFillingPeriodCircle _ _
      (p.1,A.cuspFiniteFiberCircleToFilling _ p.2) = _
    rw [hp, phasePoint]
    rfl
  rw [he, ← integralSingularHomologyMap_comp_wang,
    ← integralSingularHomologyMap_comp_wang, positiveCircleProductSwap_generator,
    map_neg, map_neg]
  congr 2
  exact (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).apply_symm_apply _

public theorem circle_homology (A : AnalyticData) (j : Fin 2) :
    integralSingularHomologyMap 1 (A.cuspFiniteFiberCircleToFilling j)
      standardCircleHomologyGenerator =
      (-(Pi.single j 1 : Fin 2 → ℤ) 0 + (Pi.single j 1 : Fin 2 → ℤ) 1) •
        loopHomologyClass ((CentralBoundary.meridianDifference A.starCuspWitness 0 2).map
          (CentralBoundary.toFilling A.starCuspWitness).continuous) +
      (-(Pi.single j 1 : Fin 2 → ℤ) 1) •
        loopHomologyClass ((CentralBoundary.meridianDifference A.starCuspWitness 1 2).map
          (CentralBoundary.toFilling A.starCuspWitness).continuous) := by
  rw [cuspFiniteFiberCircleToFilling_loop]
  exact CentralBoundary.localCuspPeriodLoop_meridianHomology A.starCuspWitness _ _ _ _

public theorem torus_homology (A : AnalyticData) (j : Fin 3) :
    integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling (index j))
      standardTwoTorusHomologyGenerator =
      -((-(Pi.single (period j) 1 : Fin 2 → ℤ) 0 +
            (Pi.single (period j) 1 : Fin 2 → ℤ) 1) •
          A.cuspFillingPhaseSweep (phase j)
            (loopHomologyClass ((CentralBoundary.meridianDifference A.starCuspWitness 0 2).map
              (CentralBoundary.toFilling A.starCuspWitness).continuous)) +
        (-(Pi.single (period j) 1 : Fin 2 → ℤ) 1) •
          A.cuspFillingPhaseSweep (phase j)
            (loopHomologyClass ((CentralBoundary.meridianDifference A.starCuspWitness 1 2).map
              (CentralBoundary.toFilling A.starCuspWitness).continuous))) := by
  calc
    _ = -A.cuspFillingPhaseSweep (phase j)
        (integralSingularHomologyMap 1
          (A.cuspFiniteFiberCircleToFilling (period j))
          standardCircleHomologyGenerator) := by
      rw [phaseSweep, neg_neg]
    _ = _ := by rw [circle_homology, map_add, map_zsmul, map_zsmul]

public theorem toFilling_circleAction (A : AnalyticData) (a : Fin 2)
    (z : UnitAddCircle) (x : CentralBoundary.Spheres) :
    CentralBoundary.toFilling A.starCuspWitness
        (CentralBoundary.circleAction A.starCuspWitness a (z,x)) =
      cuspFillingPeriodCircle A.starCuspWitness a
        (z, CentralBoundary.toFilling A.starCuspWitness x) := by
  change actualLocalCuspCentralOrbitMap A.starCuspWitness
    (CentralBoundary.homeomorph A.starCuspWitness
      (CentralBoundary.phaseMap A.starCuspWitness
        (CentralBoundary.coordinatePhase a z, x))) =
      cuspFillingPeriodCircle A.starCuspWitness a
        (z, actualLocalCuspCentralOrbitMap A.starCuspWitness
          (CentralBoundary.homeomorph A.starCuspWitness x))
  rw [CentralBoundary.homeomorph_phaseMap, cuspFillingPeriodCircle_centralOrbit]
  rfl

public theorem toFilling_circleSweep (A : AnalyticData) (a : Fin 2)
    {x : CentralBoundary.Spheres} (p : Path x x) :
    integralSingularHomologyMap 2 (CentralBoundary.toFilling A.starCuspWitness)
      (circleSweepClass (CentralBoundary.circleAction A.starCuspWitness a) p) =
        A.cuspFillingPhaseSweep a
          (loopHomologyClass (p.map (CentralBoundary.toFilling A.starCuspWitness).continuous)) := by
  let f := CentralBoundary.toFilling A.starCuspWitness
  let c := pathCircleMap p
  have hc : integralSingularHomologyMap 1 (f.comp c) standardCircleHomologyGenerator =
      loopHomologyClass (p.map f.continuous) := by
    rw [← integralSingularHomologyMap_comp_wang, pathCircleMap_homology,
      integralSingularHomologyMap_loopHomologyClass]
  change integralSingularHomologyMap 2 f
    (integralSingularHomologyMap 2 (CentralBoundary.circleAction A.starCuspWitness a)
      (normalizedCircleCross 1 (loopHomologyClass p))) =
    integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness a)
      (normalizedCircleCross 1 (loopHomologyClass (p.map f.continuous)))
  rw [← pathCircleMap_homology p, ← positiveCircleCross_eq_normalized,
    ← hc, ← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 f
    (integralSingularHomologyMap 2 (CentralBoundary.circleAction A.starCuspWitness a)
      (integralSingularHomologyMap 2 (circleProductMap c) positiveCircleProductGenerator)) =
    integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness a)
      (integralSingularHomologyMap 2 (circleProductMap (f.comp c)) positiveCircleProductGenerator)
  rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang]
  have he : f.comp ((CentralBoundary.circleAction A.starCuspWitness a).comp
      (circleProductMap c)) =
      (cuspFillingPeriodCircle A.starCuspWitness a).comp
        (circleProductMap (f.comp c)) := by
    ext q
    exact toFilling_circleAction A a q.1 (c q.2)
  exact congrArg (fun h ↦ integralSingularHomologyMap 2 h positiveCircleProductGenerator) he

end BoundaryMixedTori
end SphereSixComplex.Geometry.AnalyticData
