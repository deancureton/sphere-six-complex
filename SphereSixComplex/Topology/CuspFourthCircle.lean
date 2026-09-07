module
public import SphereSixComplex.Topology.PaperCuspFourthPeriodInvariance
public import SphereSixComplex.Topology.PaperCuspRadialClutchingConstruction
public import SphereSixComplex.Topology.FixedLoopSweepWangBoundary
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
public def cuspFourthCircle (x : PeriodDomain) : C(StdTorus 1, AdditiveTorus x.1) :=
  ((additiveTorusStdHomeomorph x.1 (fullRankDomain x)).symm : C(StdTorus 4, AdditiveTorus x.1)).comp
    (standardFourTorusCoordinateCircle 3)

public theorem cuspFourthCircle_real (x : PeriodDomain) (t : ℝ) :
    cuspFourthCircle x (fun _ ↦ (t : UnitAddCircle)) =
      additiveTorusProjection x.1 (t • periodVector x.1 ![0,0,0,1]) := by
  apply (additiveTorusStdHomeomorph x.1 (fullRankDomain x)).injective
  change (additiveTorusStdHomeomorph x.1 (fullRankDomain x))
    ((additiveTorusStdHomeomorph x.1 (fullRankDomain x)).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  change standardFourTorusCoordinateCircle 3 (fun _ ↦ (t : UnitAddCircle)) =
    periodCoordMap x.1 (fullRankDomain x) (t • periodVector x.1 ![0,0,0,1])
  ext i
  simp only [standardFourTorusCoordinateCircle, ContinuousMap.coe_mk, periodCoordMap,
    map_smul, realEquiv_symm_periodVector]
  fin_cases i <;> simp [integerToReal]

public theorem cuspFourthCircle_fixed (x : PeriodDomain) (z : StdTorus 1) :
    cuspFiberClutching x (cuspFourthCircle x z) = cuspFourthCircle x z := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) (z 0)
  have hz : z = fun _ ↦ (t : UnitAddCircle) := by
    ext i
    fin_cases i
    exact ht.symm
  rw [hz, cuspFourthCircle_real]
  change Quotient.mk _ (cuspFiberLift x (t • periodVector x.1 ![0,0,0,1])) = _
  rw [map_smul, cuspFiberLift_periodVector]
  rw [← rhoLambda_g₀_apply, rhoLambda_fourthBasis]
  rfl

public theorem cuspFourthCircle_homology (x : PeriodDomain) :
    (cuspMonodromyCoordinates x).degreeOne
      (integralSingularHomologyMap 1 (cuspFourthCircle x) standardCircleHomologyGenerator) =
      Pi.single 3 1 := by
  change stdTorusFourHomologyOne
    (integralSingularHomologyMap 1
      (additiveTorusStdHomeomorph x.1 (fullRankDomain x) : C(AdditiveTorus x.1, StdTorus 4))
      (integralSingularHomologyMap 1 (cuspFourthCircle x) standardCircleHomologyGenerator)) = _
  rw [integralSingularHomologyMap_comp_wang]
  have h : (additiveTorusStdHomeomorph x.1 (fullRankDomain x) : C(AdditiveTorus x.1, StdTorus 4)).comp
      (cuspFourthCircle x) = standardFourTorusCoordinateCircle 3 := by
    ext1 z
    exact (additiveTorusStdHomeomorph x.1 (fullRankDomain x)).apply_symm_apply _
  rw [h]
  exact standardFourTorusCoordinateHom_coordinateHomologyClass 3

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
