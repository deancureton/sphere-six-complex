module

public import SphereSixComplex.Paper.Topology.ConstructedPositiveColumnHomology
public import SphereSixComplex.Paper.Topology.CuspMixedTorusPositiveProjection

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.StandardTorusHomology
open CuspPuncturedCollarBridge CuspStraighteningRetraction
open InfiniteA2Toric

def cuspFiberSpecializationColumn (A : PaperAnalyticData) (j : Fin 4) :
    IntegralSingularHomology 2 (ActualLocalCuspFilling A.starCuspWitness) :=
  integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling j)
    standardTwoTorusHomologyGenerator

theorem cuspFiberSpecializationColumn_positive_zero (A : PaperAnalyticData) (j : Fin 3) :
    constructedCuspHomologyTwoPositiveReadout A (A.cuspFiberSpecializationColumn j.succ) = 0 := by
  have hj : cuspMixedTorusIndex j = j.succ := by fin_cases j <;> rfl
  change constructedPositiveHomologyTwoReadout A
    (integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
      (integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling j.succ)
        standardTwoTorusHomologyGenerator)) = 0
  rw [← hj, A.cuspMixedTorus_positiveProjection_zero j]
  exact map_zero _

theorem cuspFiberSpecializationColumn_positive_one (A : PaperAnalyticData) :
    constructedCuspHomologyTwoPositiveReadout A (A.cuspFiberSpecializationColumn 0) = 1 :=
  constructedPositiveHomologyTwoReadout_firstTorus A

end SphereSixComplex.Geometry.PaperAnalyticData
