module

public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundarySlant
public import SphereSixComplex.Paper.Topology.EllipticThreeTorusWangEndpointCoordinates

/-!
# Additive orbit sweeps for the elliptic three-torus clutchings
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticThreeTorusAdditiveOrbitSweep

open NormalizedFiniteOrderAdditiveCircleSweep
open PaperAffineCyclicReducedFiberMappingTorus
open StandardTorusHomology

/-- The order-three clutching as a continuous additive equivalence. -/
public def orderThreeClutchingAddEquiv : StdTorus 3 ≃ₜ+ StdTorus 3 where
  toFun := orderThreeThreeTorusClutching
  invFun := orderThreeThreeTorusClutching.symm
  left_inv := orderThreeThreeTorusClutching.left_inv
  right_inv := orderThreeThreeTorusClutching.right_inv
  map_add' x y := by
    funext i
    fin_cases i <;> simp [orderThreeThreeTorusClutching] <;> abel
  continuous_toFun := orderThreeThreeTorusClutching.continuous
  continuous_invFun := orderThreeThreeTorusClutching.symm.continuous

/-- The order-four clutching as a continuous additive equivalence. -/
public def orderFourClutchingAddEquiv : StdTorus 3 ≃ₜ+ StdTorus 3 where
  toFun := orderFourThreeTorusClutching
  invFun := orderFourThreeTorusClutching.symm
  left_inv := orderFourThreeTorusClutching.left_inv
  right_inv := orderFourThreeTorusClutching.right_inv
  map_add' x y := by
    funext i
    fin_cases i <;> simp [orderFourThreeTorusClutching] <;> abel
  continuous_toFun := orderFourThreeTorusClutching.continuous
  continuous_invFun := orderFourThreeTorusClutching.symm.continuous

@[simp]
public theorem orderThreeClutchingAddEquiv_toHomeomorph :
    orderThreeClutchingAddEquiv.toHomeomorph = orderThreeThreeTorusClutching := rfl

@[simp]
public theorem orderFourClutchingAddEquiv_toHomeomorph :
    orderFourClutchingAddEquiv.toHomeomorph = orderFourThreeTorusClutching := rfl

public theorem orderThreeClutchingAddEquiv_pow :
    orderThreeClutchingAddEquiv.toHomeomorph ^ 3 = 1 :=
  orderThreeThreeTorusClutching_pow

public theorem orderFourClutchingAddEquiv_pow :
    orderFourClutchingAddEquiv.toHomeomorph ^ 4 = 1 :=
  orderFourThreeTorusClutching_pow



private def coordinateCircleTwo : C(StdTorus 1, StdTorus 3) where
  toFun x := ![0, 0, x 0]
  continuous_toFun := by fun_prop



private theorem standardThreeTorusCoordinateCircle_two :
    standardThreeTorusCoordinateCircle 2 = coordinateCircleTwo := by
  ext x j
  fin_cases j <;> rfl



public def orderThreeFixedCoordinateTwo : fixedLoops orderThreeClutchingAddEquiv :=
  ⟨standardThreeTorusCoordinateCircle 2, by
    apply LinearMap.mem_ker.mpr
    ext x j
    fin_cases j <;>
      simp [loopAction, orderThreeClutchingAddEquiv,
        orderThreeThreeTorusClutching, standardThreeTorusCoordinateCircle_two,
        coordinateCircleTwo]⟩

public def orderFourFixedCoordinateTwo : fixedLoops orderFourClutchingAddEquiv :=
  ⟨standardThreeTorusCoordinateCircle 2, by
    apply LinearMap.mem_ker.mpr
    ext x j
    fin_cases j <;>
      simp [loopAction, orderFourClutchingAddEquiv,
        orderFourThreeTorusClutching, standardThreeTorusCoordinateCircle_two,
        coordinateCircleTwo]⟩



end SphereSixComplex.Topology.EllipticThreeTorusAdditiveOrbitSweep

end

end
