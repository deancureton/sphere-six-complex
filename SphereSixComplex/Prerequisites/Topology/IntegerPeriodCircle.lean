module
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.StandardTorusHomology
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

end SphereSixComplex.StandardTorusHomology
end
