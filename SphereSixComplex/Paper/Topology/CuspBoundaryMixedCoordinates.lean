module

public import SphereSixComplex.Paper.Topology.CuspBoundaryMixedTori
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberHomologyCoordinates

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

theorem fillingHomologyTwoEquiv_toFilling
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (x : IntegralSingularHomology 2 CentralBoundary.Spheres) :
    CentralFiberHomology.fillingHomologyTwoEquiv W R
      (integralSingularHomologyMap 2 (CentralBoundary.toFilling W) x) =
      Fin.cons 0 (CentralBoundary.homologyTwoEquiv W x) := by
  have h := CentralFiberHomology.fillingHomologyTwoEquiv_boundaryInclusion W R
    (integralSingularHomologyMap 2
      ⟨CentralBoundary.homeomorph W, (CentralBoundary.homeomorph W).continuous⟩ x)
  erw [integralSingularHomologyMap_comp_wang] at h
  change CentralFiberHomology.fillingHomologyTwoEquiv W R
      (integralSingularHomologyMap 2 (CentralBoundary.toFilling W) x) = _ at h
  rw [h]
  congr 1
  exact congrArg (CentralBoundary.homologyTwoEquiv W)
    ((integralSingularHomologyEquiv 2 (CentralBoundary.homeomorph W)).symm_apply_apply x)

theorem fillingHomologyTwoEquiv_meridianSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (R : ActualLocalCuspCentralFiberRetractionData W) (a : Fin 2) (i j : Fin 3) :
    CentralFiberHomology.fillingHomologyTwoEquiv W R
      (integralSingularHomologyMap 2 (CentralBoundary.toFilling W)
        (CentralBoundary.meridianSweep W a i j)) =
      Fin.cons 0 (Pi.single i (CentralBoundary.phaseWeights a i) -
        Pi.single j (CentralBoundary.phaseWeights a j)) := by
  rw [fillingHomologyTwoEquiv_toFilling, CentralBoundary.homologyTwoEquiv_meridianSweep]

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace SphereSixComplex.Geometry.AnalyticData.BoundaryMixedTori
open InfiniteA2Toric.Construction CuspCollar
open SphereSixComplex.Topology CircleProductIdentityMappingTorus
open StandardCircleHomologyLiftDegree SphereSixComplex.StandardTorusHomology

theorem fillingHomologyTwoEquiv_phaseSweep
    (A : AnalyticData) (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness)
    (a : Fin 2) (i j : Fin 3) :
    CentralFiberHomology.fillingHomologyTwoEquiv A.starCuspWitness R
      (A.cuspFillingPhaseSweep a
        (loopHomologyClass ((CentralBoundary.meridianDifference A.starCuspWitness i j).map
          (CentralBoundary.toFilling A.starCuspWitness).continuous))) =
      -Fin.cons 0 (Pi.single i (CentralBoundary.phaseWeights a i) -
        Pi.single j (CentralBoundary.phaseWeights a j)) := by
  rw [← toFilling_circleSweep]
  have h := CentralBoundary.meridianSweep_eq_neg_circleSweepClass A.starCuspWitness a i j
  have hh : circleSweepClass (CentralBoundary.circleAction A.starCuspWitness a)
      (CentralBoundary.meridianDifference A.starCuspWitness i j) =
      -CentralBoundary.meridianSweep A.starCuspWitness a i j := by
    rw [h, neg_neg]
    rfl
  rw [hh, map_neg, map_neg, fillingHomologyTwoEquiv_meridianSweep]

theorem fillingHomologyTwoEquiv_mixedTorus
    (A : AnalyticData) (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness)
    (j : Fin 3) :
    CentralFiberHomology.fillingHomologyTwoEquiv A.starCuspWitness R
      (integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling (index j))
        standardTwoTorusHomologyGenerator) =
      ![![0, 1, 0, 1], ![0, -1, -1, 0], ![0, 1, 0, 0]] j := by
  rw [torus_homology, map_neg, map_add, map_zsmul, map_zsmul,
    fillingHomologyTwoEquiv_phaseSweep, fillingHomologyTwoEquiv_phaseSweep]
  ext k
  fin_cases j <;> fin_cases k <;>
    norm_num [period, phase, CentralBoundary.phaseWeights, Pi.single_apply]
  all_goals decide

end SphereSixComplex.Geometry.AnalyticData.BoundaryMixedTori
