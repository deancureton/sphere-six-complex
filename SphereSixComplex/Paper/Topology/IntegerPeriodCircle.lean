module

public import SphereSixComplex.Prerequisites.Topology.IntegerPeriodCircle
public import SphereSixComplex.Paper.Topology.PaperEllipticTorusHomologyBasisProof

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.EllipticFamilySpecialization
open StandardCircleHomologyLiftDegree

public def integerPeriodCircle (x : Parameters) (h : FullRank x) (n : IntegerPeriods) :
    C(StdTorus 1, AdditiveTorus x) :=
  ((additiveTorusStdHomeomorph x h).symm : C(StdTorus 4, AdditiveTorus x)).comp
    (integerCoordinateCircle n)

public theorem integerPeriodCircle_real (x : Parameters) (h : FullRank x)
    (n : IntegerPeriods) (t : ℝ) :
    integerPeriodCircle x h n (fun _ ↦ (t : UnitAddCircle)) =
      additiveTorusProjection x (t • periodVector x n) := by
  apply (additiveTorusStdHomeomorph x h).injective
  rw [show (additiveTorusStdHomeomorph x h)
    (integerPeriodCircle x h n (fun _ ↦ (t : UnitAddCircle))) =
      integerCoordinateCircle n (fun _ ↦ (t : UnitAddCircle)) from
        (additiveTorusStdHomeomorph x h).apply_symm_apply _]
  change integerCoordinateCircle n (fun _ ↦ (t : UnitAddCircle)) = periodCoordMap x h (t • periodVector x n)
  ext j
  simp [integerCoordinateCircle, periodCoordMap, map_smul, realEquiv_symm_periodVector,
    integerToReal, ← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm]

public theorem integerPeriodCircle_homology (x : Parameters) (h : FullRank x)
    (n : IntegerPeriods) :
    additiveTorusHomologyDegreeOne x h
      (integralSingularHomologyMap 1 (integerPeriodCircle x h n)
        standardCircleHomologyGenerator) = n := by
  change stdTorusFourHomologyOne
    (integralSingularHomologyMap 1
      (additiveTorusStdHomeomorph x h : C(AdditiveTorus x, StdTorus 4))
      (integralSingularHomologyMap 1 (integerPeriodCircle x h n)
        standardCircleHomologyGenerator)) = n
  rw [integralSingularHomologyMap_comp_wang]
  have hc : (additiveTorusStdHomeomorph x h : C(AdditiveTorus x, StdTorus 4)).comp
      (integerPeriodCircle x h n) = integerCoordinateCircle n := by
    ext1 z
    exact (additiveTorusStdHomeomorph x h).apply_symm_apply _
  rw [hc]
  exact integerCoordinateCircle_homology n

end SphereSixComplex.StandardTorusHomology
end
