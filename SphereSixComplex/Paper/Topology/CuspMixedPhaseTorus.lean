module
public import SphereSixComplex.Paper.Topology.CuspFillingPhaseCircle
public import SphereSixComplex.Prerequisites.Topology.PositiveCircleProductSwap
import all SphereSixComplex.Paper.Periods.Matrix

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus GlobalTorusFamily
open CuspCollar CuspRadialClutchingConstruction CuspPeriodExpansion
open PositiveCircleCross CircleProductIdentityMappingTorus




public def cuspFillingPhaseSweep (A : AnalyticData) (i : Fin 2) :
    IntegralSingularHomology 1 (ActualLocalCuspFilling A.starCuspWitness) →+
      IntegralSingularHomology 2 (ActualLocalCuspFilling A.starCuspWitness) :=
  (integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness i)).comp
    (normalizedCircleCross 1)


end SphereSixComplex.Geometry.AnalyticData
