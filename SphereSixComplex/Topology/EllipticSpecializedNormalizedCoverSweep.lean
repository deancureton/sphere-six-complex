module

public import SphereSixComplex.Topology.EllipticThreeTorusExplicitOrbitSweepHomology
public import SphereSixComplex.Topology.FixedLoopSweepAdditivityReduction
public import SphereSixComplex.Topology.NormalizedCoverCrossLowOverlapCalculationProof

/-!
# Specialized normalized-cover sweeps for the elliptic clutchings

The explicit normalized-cover calculation on a fixed loop, together with the concrete
order-three and order-four cross-coordinate relations, identifies the two cross classes used
in the elliptic degree-two basis calculation.  Cancellation is justified by the explicit
rank-two coordinates on the corresponding mapping-torus homology groups.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticSpecializedNormalizedCoverSweep

open EllipticThreeTorusAdditiveOrbitSweep
open EllipticThreeTorusExplicitOrbitSweepHomology
open EllipticThreeTorusRankOneMappingTorusCoordinates
open FixedLoopSweepWangBoundary
open NormalizedAffineMappingTorusCover
open NormalizedCoverCrossLowOverlapCalculationProof
open NormalizedFiniteOrderAdditiveCircleSweepProof
open PaperAffineCyclicReducedFiberMappingTorus
open PositiveCircleCross
open StandardTorusHomology

/-- The explicit fixed-loop sweep selected by the invariant coordinate at order three. -/
public noncomputable def orderThreeFixedLoopSweep :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) :=
  fixedLoopSweepClass orderThreeClutchingAddEquiv orderThreeFixedCoordinateTwo

/-- The explicit fixed-loop sweep selected by the invariant coordinate at order four. -/
public noncomputable def orderFourFixedLoopSweep :
    IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching) :=
  fixedLoopSweepClass orderFourClutchingAddEquiv orderFourFixedCoordinateTwo

private theorem orderThreeFixedLoopSweep_positiveInvariant :
    orderThreeInvariantsEquivInt
        (OrderThreePresentation.totalToInvariants orderThreeFixedLoopSweep) = 1 := by
  change standardThreeTorusHomologyOne
      (OrderThreePresentation.boundary orderThreeFixedLoopSweep) 2 = 1
  have hboundary : OrderThreePresentation.boundary orderThreeFixedLoopSweep =
      standardThreeTorusCoordinateHomologyClass 2 := by
    change (circleMappingTorusWangPresentationOfCover
      orderThreeThreeTorusClutching 1).boundary
        (fixedLoopSweepClass orderThreeClutchingAddEquiv
          orderThreeFixedCoordinateTwo) = _
    convert fixedLoopSweepClass_boundary orderThreeClutchingAddEquiv
      orderThreeFixedCoordinateTwo using 1 <;> rfl
  rw [hboundary]
  change standardThreeTorusDegreeOneCoordinateHom
      (standardThreeTorusCoordinateHomologyClass 2) 2 = 1
  rw [standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  simp

private theorem orderFourFixedLoopSweep_positiveInvariant :
    orderFourInvariantsEquivInt
        (OrderFourPresentation.totalToInvariants orderFourFixedLoopSweep) = 1 := by
  change standardThreeTorusHomologyOne
      (OrderFourPresentation.boundary orderFourFixedLoopSweep) 2 = 1
  have hboundary : OrderFourPresentation.boundary orderFourFixedLoopSweep =
      standardThreeTorusCoordinateHomologyClass 2 := by
    change (circleMappingTorusWangPresentationOfCover
      orderFourThreeTorusClutching 1).boundary
        (fixedLoopSweepClass orderFourClutchingAddEquiv
          orderFourFixedCoordinateTwo) = _
    convert fixedLoopSweepClass_boundary orderFourClutchingAddEquiv
      orderFourFixedCoordinateTwo using 1 <;> rfl
  rw [hboundary]
  change standardThreeTorusDegreeOneCoordinateHom
      (standardThreeTorusCoordinateHomologyClass 2) 2 = 1
  rw [standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  simp

private noncomputable def orderThreeFixedLoopSweepCoordinates :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  orderThreeTotalAddEquiv orderThreeFixedLoopSweep
    orderThreeFixedLoopSweep_positiveInvariant

private noncomputable def orderFourFixedLoopSweepCoordinates :
    IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  orderFourTotalAddEquiv orderFourFixedLoopSweep
    orderFourFixedLoopSweep_positiveInvariant

private theorem orderThree_three_nsmul_cancel
    {x y : IntegralSingularHomology 2
      (CircleMappingTorus orderThreeThreeTorusClutching)}
    (h : 3 • x = 3 • y) : x = y := by
  apply orderThreeFixedLoopSweepCoordinates.injective
  have h' := congrArg orderThreeFixedLoopSweepCoordinates h
  rw [map_nsmul, map_nsmul] at h'
  funext i
  have hi := congrFun h' i
  have hi' : (3 : ℤ) * orderThreeFixedLoopSweepCoordinates x i =
      (3 : ℤ) * orderThreeFixedLoopSweepCoordinates y i := by
    simpa [nsmul_eq_mul] using hi
  exact Int.eq_of_mul_eq_mul_left (by norm_num) hi'

private theorem orderFour_two_nsmul_cancel
    {x y : IntegralSingularHomology 2
      (CircleMappingTorus orderFourThreeTorusClutching)}
    (h : 2 • x = 2 • y) : x = y := by
  apply orderFourFixedLoopSweepCoordinates.injective
  have h' := congrArg orderFourFixedLoopSweepCoordinates h
  rw [map_nsmul, map_nsmul] at h'
  funext i
  have hi := congrFun h' i
  have hi' : (2 : ℤ) * orderFourFixedLoopSweepCoordinates x i =
      (2 : ℤ) * orderFourFixedLoopSweepCoordinates y i := by
    simpa [nsmul_eq_mul] using hi
  exact Int.eq_of_mul_eq_mul_left (by norm_num) hi'

/-- At order three, the normalized-cover cross of the first coordinate is exactly the explicit
fixed-loop sweep of the invariant third coordinate. -/
public theorem orderThreeNormalizedCross_one_eq_fixedLoopSweep :
    orderThreeNormalizedCross 1 = orderThreeFixedLoopSweep := by
  apply orderThree_three_nsmul_cancel
  rw [← orderThreeNormalizedCross_two_eq_three_one]
  have hfixed := normalizedAffineCover_positiveCircleCross_fixed 3
    orderThreeClutchingAddEquiv orderThreeClutchingAddEquiv_pow
    orderThreeFixedCoordinateTwo
  have hfixed' : integralSingularHomologyMap 2
      (normalizedAffineCoverToCircleMappingTorus
        orderThreeClutchingAddEquiv.toHomeomorph orderThreeClutchingAddEquiv_pow)
      (positiveCircleCross orderThreeFixedCoordinateTwo.1) =
        3 • fixedLoopSweepClass orderThreeClutchingAddEquiv
          orderThreeFixedCoordinateTwo := by
    simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using hfixed
  convert hfixed' using 1 <;> rfl

/-- At order four, the normalized-cover cross of the first orbit coordinate is twice the
primitive explicit fixed-loop sweep. -/
public theorem orderFourNormalizedCross_zero_eq_two_fixedLoopSweep :
    orderFourNormalizedCross 0 = 2 • orderFourFixedLoopSweep := by
  apply orderFour_two_nsmul_cancel
  rw [← orderFourNormalizedCross_two_eq_two_zero]
  calc
    orderFourNormalizedCross 2 =
        (4 : ℤ) • orderFourFixedLoopSweep :=
      by
        convert normalizedAffineCover_positiveCircleCross_fixed 4
          orderFourClutchingAddEquiv orderFourClutchingAddEquiv_pow
          orderFourFixedCoordinateTwo using 1 <;> rfl
    _ = 2 • (2 • orderFourFixedLoopSweep) := by
      rw [ofNat_zsmul, ← mul_nsmul]

end SphereSixComplex.Topology.EllipticSpecializedNormalizedCoverSweep

end

end
