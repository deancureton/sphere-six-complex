module
public import SphereSixComplex.Paper.Topology.PaperCuspRadialClutchingConstruction
public import SphereSixComplex.Prerequisites.Topology.FixedLoopSweepWangBoundary


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
public def cuspCoordinateCircle (x : PeriodDomain) (i : Fin 4) : C(StdTorus 1, AdditiveTorus x.1) :=
  ((additiveTorusStdHomeomorph x.1 (fullRankDomain x)).symm : C(StdTorus 4, AdditiveTorus x.1)).comp
    (standardFourTorusCoordinateCircle i)

public theorem cuspCoordinateCircle_real (x : PeriodDomain) (i : Fin 4) (t : ℝ) :
    cuspCoordinateCircle x i (fun _ ↦ (t : UnitAddCircle)) =
      additiveTorusProjection x.1 (t • periodVector x.1 (Pi.single i 1)) := by
  apply (additiveTorusStdHomeomorph x.1 (fullRankDomain x)).injective
  change (additiveTorusStdHomeomorph x.1 (fullRankDomain x))
    ((additiveTorusStdHomeomorph x.1 (fullRankDomain x)).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  change standardFourTorusCoordinateCircle i (fun _ ↦ (t : UnitAddCircle)) =
    periodCoordMap x.1 (fullRankDomain x) (t • periodVector x.1 (Pi.single i 1))
  ext j
  simp only [standardFourTorusCoordinateCircle, ContinuousMap.coe_mk, periodCoordMap,
    map_smul, realEquiv_symm_periodVector]
  fin_cases i <;> fin_cases j <;> simp [integerToReal]

public theorem cuspCoordinateCircle_fixed (x : PeriodDomain) (i : Fin 4)
    (hi : rhoLambda g₀ (Pi.single i 1) = Pi.single i 1) (z : StdTorus 1) :
    cuspFiberClutching x (cuspCoordinateCircle x i z) = cuspCoordinateCircle x i z := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) (z 0)
  have hz : z = fun _ ↦ (t : UnitAddCircle) := by
    ext i
    fin_cases i
    exact ht.symm
  rw [hz, cuspCoordinateCircle_real]
  change Quotient.mk _ (cuspFiberLift x (t • periodVector x.1 (Pi.single i 1))) = _
  rw [map_smul, cuspFiberLift_periodVector]
  rw [← rhoLambda_g₀_apply, hi]
  rfl

public theorem cuspCoordinateCircle_homology (x : PeriodDomain) (i : Fin 4) :
    (cuspMonodromyCoordinates x).degreeOne
      (integralSingularHomologyMap 1 (cuspCoordinateCircle x i) standardCircleHomologyGenerator) =
      Pi.single i 1 := by
  change stdTorusFourHomologyOne
    (integralSingularHomologyMap 1
      (additiveTorusStdHomeomorph x.1 (fullRankDomain x) : C(AdditiveTorus x.1, StdTorus 4))
      (integralSingularHomologyMap 1 (cuspCoordinateCircle x i) standardCircleHomologyGenerator)) = _
  rw [integralSingularHomologyMap_comp_wang]
  have h : (additiveTorusStdHomeomorph x.1 (fullRankDomain x) : C(AdditiveTorus x.1, StdTorus 4)).comp
      (cuspCoordinateCircle x i) = standardFourTorusCoordinateCircle i := by
    ext1 z
    exact (additiveTorusStdHomeomorph x.1 (fullRankDomain x)).apply_symm_apply _
  rw [h]
  exact standardFourTorusCoordinateHom_coordinateHomologyClass i

open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary
public def cuspCoordinateFixedCircle (x : PeriodDomain) (i : Fin 4)
    (hi : rhoLambda g₀ (Pi.single i 1) = Pi.single i 1) :
    FixedTopologicalCircle (cuspFiberClutching x) :=
  ⟨cuspCoordinateCircle x i, cuspCoordinateCircle_fixed x i hi⟩

public theorem cuspCoordinateSweep_wang (x : PeriodDomain) (i : Fin 4)
    (hi : rhoLambda g₀ (Pi.single i 1) = Pi.single i 1) :
    (cuspMonodromyCoordinates x).degreeOne
      ((circleMappingTorusWangPresentationOfCover (cuspFiberClutching x) 1).boundary
        (fixedLoopSweepClass (cuspFiberClutching x) (cuspCoordinateFixedCircle x i hi))) =
      Pi.single i 1 := by
  rw [fixedLoopSweepClass_boundary]
  exact cuspCoordinateCircle_homology x i

end SphereSixComplex.Geometry.CuspRadialClutchingConstruction
end
end
