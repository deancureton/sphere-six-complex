module
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.EllipticFamilySpecialization
open StandardCircleHomologyLiftDegree

public def integerCoordinateCircle (n : Fin 4 → ℤ) : C(StdTorus 1, StdTorus 4) :=
  ⟨fun z i ↦ n i • z 0, continuous_pi (fun i ↦ (continuous_apply 0).zsmul (n i))⟩

public theorem integerCoordinateCircle_homology (n : Fin 4 → ℤ) :
    stdTorusFourHomologyOne
      (integralSingularHomologyMap 1 (integerCoordinateCircle n)
        standardCircleHomologyGenerator) = n := by
  funext i
  change unitCircleHomologyWinding
    (integralSingularHomologyMap 1
      (stdTorusOneHomeomorph : C(StdTorus 1, UnitAddCircle))
      (integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection i)
        (integralSingularHomologyMap 1 (integerCoordinateCircle n)
          standardCircleHomologyGenerator))) = n i
  rw [integralSingularHomologyMap_comp_wang 1 (integerCoordinateCircle n)]
  have h := standardCircleHomologyGenerator_map_of_additiveLift
    ((standardFourTorusCoordinateProjection i).comp (integerCoordinateCircle n))
    ((n i : ℝ) • (AddMonoidHom.id ℝ)) (n i) ?_ ?_
  · rw [h, map_zsmul, map_zsmul, standardCircleHomologyGenerator_winding]
    simp
  · intro r
    ext j
    change n i • (r : UnitAddCircle) = (((n i : ℝ) * r : ℝ) : UnitAddCircle)
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  · simp

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
