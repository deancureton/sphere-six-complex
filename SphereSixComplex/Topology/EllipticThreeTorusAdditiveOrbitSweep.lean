module

public import SphereSixComplex.Topology.CanonicalProductWangBoundarySlant
public import SphereSixComplex.Topology.EllipticThreeTorusWangEndpointCoordinates

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

private def coordinateCircleZero : C(StdTorus 1, StdTorus 3) where
  toFun x := ![x 0, 0, 0]
  continuous_toFun := by fun_prop

private def coordinateCircleOne : C(StdTorus 1, StdTorus 3) where
  toFun x := ![0, x 0, 0]
  continuous_toFun := by fun_prop

private def coordinateCircleTwo : C(StdTorus 1, StdTorus 3) where
  toFun x := ![0, 0, x 0]
  continuous_toFun := by fun_prop

private theorem standardThreeTorusCoordinateCircle_zero :
    standardThreeTorusCoordinateCircle 0 = coordinateCircleZero := by
  ext x j
  fin_cases j <;> rfl

private theorem standardThreeTorusCoordinateCircle_one :
    standardThreeTorusCoordinateCircle 1 = coordinateCircleOne := by
  ext x j
  fin_cases j <;> rfl

private theorem standardThreeTorusCoordinateCircle_two :
    standardThreeTorusCoordinateCircle 2 = coordinateCircleTwo := by
  ext x j
  fin_cases j <;> rfl

public theorem orderThreeOrbitNorm_coordinateOne :
    (∑ i ∈ Finset.range 3, ((loopAction orderThreeClutchingAddEquiv) ^ i)
      (standardThreeTorusCoordinateCircle 1)) =
        standardThreeTorusCoordinateCircle 2 := by
  rw [standardThreeTorusCoordinateCircle_one,
    standardThreeTorusCoordinateCircle_two]
  ext x j
  fin_cases j <;>
    simp [Finset.sum_range_succ, loopAction, orderThreeClutchingAddEquiv,
      orderThreeThreeTorusClutching, coordinateCircleOne, coordinateCircleTwo,
      pow_succ]

public theorem orderFourOrbitNorm_coordinateZero :
    (∑ i ∈ Finset.range 4, ((loopAction orderFourClutchingAddEquiv) ^ i)
      (standardThreeTorusCoordinateCircle 0)) =
        2 • standardThreeTorusCoordinateCircle 2 := by
  rw [standardThreeTorusCoordinateCircle_zero,
    standardThreeTorusCoordinateCircle_two]
  ext x j
  fin_cases j <;>
    simp [Finset.sum_range_succ, loopAction, orderFourClutchingAddEquiv,
      orderFourThreeTorusClutching, coordinateCircleZero, coordinateCircleTwo,
      pow_succ]
  all_goals abel

public def orderThreeFixedCoordinateTwo : FixedLoop orderThreeClutchingAddEquiv :=
  ⟨standardThreeTorusCoordinateCircle 2, by
    apply LinearMap.mem_ker.mpr
    ext x j
    fin_cases j <;>
      simp [loopAction, orderThreeClutchingAddEquiv,
        orderThreeThreeTorusClutching, standardThreeTorusCoordinateCircle_two,
        coordinateCircleTwo]⟩

public def orderFourFixedCoordinateTwo : FixedLoop orderFourClutchingAddEquiv :=
  ⟨standardThreeTorusCoordinateCircle 2, by
    apply LinearMap.mem_ker.mpr
    ext x j
    fin_cases j <;>
      simp [loopAction, orderFourClutchingAddEquiv,
        orderFourThreeTorusClutching, standardThreeTorusCoordinateCircle_two,
        coordinateCircleTwo]⟩

public theorem orderThreeOrbitNorm_eq_fixedCoordinateTwo
    : orbitNorm 3 orderThreeClutchingAddEquiv orderThreeClutchingAddEquiv_pow
        (standardThreeTorusCoordinateCircle 1) =
      orderThreeFixedCoordinateTwo := by
  apply Subtype.ext
  rw [orbitNorm_value, orderThreeOrbitNorm_coordinateOne]
  rfl

public theorem orderFourOrbitNorm_eq_two_fixedCoordinateTwo
    : orbitNorm 4 orderFourClutchingAddEquiv orderFourClutchingAddEquiv_pow
        (standardThreeTorusCoordinateCircle 0) =
      2 • orderFourFixedCoordinateTwo := by
  apply Subtype.ext
  rw [orbitNorm_value, orderFourOrbitNorm_coordinateZero]
  rfl

end SphereSixComplex.Topology.EllipticThreeTorusAdditiveOrbitSweep

end

end
