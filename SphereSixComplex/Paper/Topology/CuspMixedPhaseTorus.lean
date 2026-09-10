module
public import SphereSixComplex.Paper.Topology.CuspFillingPhaseCircle
public import SphereSixComplex.Prerequisites.Topology.PositiveCircleProductSwap
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
import all SphereSixComplex.Paper.Periods.Matrix

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus GlobalTorusFamily
open CuspPuncturedCollarBridge CuspRadialClutchingConstruction CuspPeriodExpansion
open PositiveCircleCross CircleProductIdentityMappingTorus

public def cuspFirstPeriodFillingCircle (A : PaperAnalyticData) :
    C(StdTorus 1,actualLocalCuspFilling A.starCuspWitness) :=
  (A.cuspFiniteFiberTorusToFilling 1).comp
    ⟨fun z ↦ ![z 0,0], by fun_prop⟩

public theorem cuspFirstPeriodFillingCircle_real (A : PaperAnalyticData) (t : ℝ) :
    A.cuspFirstPeriodFillingCircle (fun _ ↦ (t : UnitAddCircle)) =
      puncturedLocalCuspToFilling A.starCuspWitness
        (actualCuspCollarPeriodPoint A.starCuspWitness
          (CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness).markingParameter_mem
          (t • periodVector (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1 (Pi.single 0 1))) := by
  change A.cuspFiniteFiberTorusToFilling 1 ![(t : UnitAddCircle),(0 : ℝ)] = _
  rw [cuspFiniteFiberTorusToFilling_real, zero_smul, add_zero]
  rfl

public theorem cuspFourthCircle_firstPeriod (A : PaperAnalyticData) (t s : UnitAddCircle) :
    cuspFillingPeriodCircle A.starCuspWitness 1 (s,A.cuspFirstPeriodFillingCircle (fun _ ↦ t)) =
      A.cuspFiniteFiberTorusToFilling 1 ![t,s] := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective s
  rw [cuspFirstPeriodFillingCircle_real, cuspFillingPeriodCircle_periodPoint,
    cuspFiniteFiberTorusToFilling_real]
  congr 2
  change _ + Pi.single (1 : Fin 2) (s : ℂ) =
    _ + s • periodVector _ (Pi.single (3 : Fin 4) 1)
  congr 1
  ext i
  fin_cases i <;> simp [periodVector, periodMatrix, Matrix.vecHead, Matrix.vecTail]

public def cuspFillingPhaseSweep (A : PaperAnalyticData) (i : Fin 2) :
    IntegralSingularHomology 1 (actualLocalCuspFilling A.starCuspWitness) →+
      IntegralSingularHomology 2 (actualLocalCuspFilling A.starCuspWitness) :=
  (integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness i)).comp
    (normalizedCircleCross 1)

public theorem cuspMixedFourthTorus_phaseSweep (A : PaperAnalyticData) :
    A.cuspFillingPhaseSweep 1
      (integralSingularHomologyMap 1 A.cuspFirstPeriodFillingCircle standardCircleHomologyGenerator) =
      -integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling 1)
        standardTwoTorusHomologyGenerator := by
  change integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness 1)
    (normalizedCircleCross 1 _) = _
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 _
    (integralSingularHomologyMap 2 (circleProductMap A.cuspFirstPeriodFillingCircle)
      positiveCircleProductGenerator) = _
  rw [integralSingularHomologyMap_comp_wang]
  have he : (cuspFillingPeriodCircle A.starCuspWitness 1).comp
      (circleProductMap A.cuspFirstPeriodFillingCircle) =
      (A.cuspFiniteFiberTorusToFilling 1).comp
        ((circleProdStandardCircleHomeomorph : C(_, _)).comp positiveCircleProductSwap) := by
    ext1 p
    have hp : p.2 = (fun _ ↦ p.2 0) := by ext i; fin_cases i; rfl
    change cuspFillingPeriodCircle _ _ (p.1,A.cuspFirstPeriodFillingCircle p.2) = _
    rw [hp, cuspFourthCircle_firstPeriod]
    rfl
  rw [he, ← integralSingularHomologyMap_comp_wang,
    ← integralSingularHomologyMap_comp_wang, positiveCircleProductSwap_generator, map_neg,
    map_neg]
  congr 2
  exact (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).apply_symm_apply _

end SphereSixComplex.Geometry.PaperAnalyticData
