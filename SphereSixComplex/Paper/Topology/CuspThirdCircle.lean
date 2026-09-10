module
public import SphereSixComplex.Paper.Topology.CuspInvariantCoordinateCircle
import all SphereSixComplex.Paper.LatticeData

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.StandardTorusHomology SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.TriangleGroup SphereSixComplex.LatticeData
open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary

public theorem cuspThirdCoordinate_fixed :
    rhoLambda g₀ (Pi.single (2 : Fin 4) 1) = Pi.single 2 1 := by
  rw [rhoLambda_g₀_apply]
  ext i
  fin_cases i <;> norm_num [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply] <;> decide

public def cuspThirdFixedCircle (x : PeriodDomain) :
    FixedTopologicalCircle (cuspFiberClutching x) :=
  cuspCoordinateFixedCircle x 2 cuspThirdCoordinate_fixed

public theorem cuspThirdSweep_wang (x : PeriodDomain) :
    (cuspMonodromyCoordinates x).degreeOne
      ((circleMappingTorusWangPresentationOfCover (cuspFiberClutching x) 1).boundary
        (fixedLoopSweepClass (cuspFiberClutching x) (cuspThirdFixedCircle x))) =
      Pi.single 2 1 := cuspCoordinateSweep_wang x 2 cuspThirdCoordinate_fixed

end SphereSixComplex.Geometry.CuspRadialClutchingConstruction
end
end
