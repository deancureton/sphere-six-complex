module
public import SphereSixComplex.Paper.Topology.PaperCuspFourthPeriodInvariance
public import SphereSixComplex.Paper.Topology.CuspInvariantCoordinateCircle
/-! The fourth period circle is fixed pointwise by the actual cusp clutching map. Its swept torus has Wang boundary equal to the fourth lattice basis vector. -/

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.StandardTorusHomology SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
private theorem fourthCoordinate_eq :
    Pi.single (3 : Fin 4) (1 : ℤ) = ![0,0,0,1] := by
  ext i
  fin_cases i <;> simp

public def cuspFourthCircle (x : PeriodDomain) : C(StdTorus 1, AdditiveTorus x.1) :=
  cuspCoordinateCircle x 3

public theorem cuspFourthCircle_real (x : PeriodDomain) (t : ℝ) :
    cuspFourthCircle x (fun _ ↦ (t : UnitAddCircle)) =
      additiveTorusProjection x.1 (t • periodVector x.1 ![0,0,0,1]) := by
  simpa only [cuspFourthCircle, fourthCoordinate_eq] using cuspCoordinateCircle_real x 3 t

public theorem cuspFourthCircle_fixed (x : PeriodDomain) (z : StdTorus 1) :
    cuspFiberClutching x (cuspFourthCircle x z) = cuspFourthCircle x z :=
  cuspCoordinateCircle_fixed x 3 (by rw [fourthCoordinate_eq]; exact rhoLambda_fourthBasis g₀) z

public theorem cuspFourthCircle_homology (x : PeriodDomain) :
    (cuspMonodromyCoordinates x).degreeOne
      (integralSingularHomologyMap 1 (cuspFourthCircle x) standardCircleHomologyGenerator) =
      Pi.single 3 1 := cuspCoordinateCircle_homology x 3

open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary
public def cuspFourthFixedCircle (x : PeriodDomain) :
    FixedTopologicalCircle (cuspFiberClutching x) :=
  ⟨cuspFourthCircle x, cuspFourthCircle_fixed x⟩

public theorem cuspFourthSweep_wang (x : PeriodDomain) :
    (cuspMonodromyCoordinates x).degreeOne
      ((circleMappingTorusWangPresentationOfCover (cuspFiberClutching x) 1).boundary
        (fixedLoopSweepClass (cuspFiberClutching x) (cuspFourthFixedCircle x))) =
      Pi.single 3 1 := by
  rw [fixedLoopSweepClass_boundary]
  exact cuspFourthCircle_homology x

end SphereSixComplex.Geometry.CuspRadialClutchingConstruction
end
end
