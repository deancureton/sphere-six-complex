module

public import SphereSixComplex.Topology.RankOneWangHomologySplitting
public import SphereSixComplex.Topology.EllipticThreeTorusWangEndpointCoordinates

/-!
# Rank-one coordinates for the elliptic three-torus mapping tori

The Wang end terms for the order-three and order-four clutchings are each infinite cyclic.  This
module transports their explicit lattice coordinates to singular homology and normalizes the
middle term by a chosen lift of the positive invariant generator.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology.EllipticThreeTorusRankOneMappingTorusCoordinates

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.WangHomologyPresentation
open EllipticThreeTorusClutchingDegreeTwo
open EllipticThreeTorusWangEndpointCoordinates
open EllipticThreeTorusWangLattice
open PaperAffineCyclicReducedFiberMappingTorus
open SphereSixComplex.StandardTorusHomology

public abbrev OrderThreePresentation :=
  circleMappingTorusWangPresentationOfCover orderThreeThreeTorusClutching 1

public abbrev OrderFourPresentation :=
  circleMappingTorusWangPresentationOfCover orderFourThreeTorusClutching 1

/-- The upper coinvariant of the order-three Wang sequence, in its positive integral coordinate. -/
public noncomputable def orderThreeCoinvariantsEquivInt :
    OrderThreePresentation.Coinvariants ≃ₗ[ℤ] ℤ :=
  (coinvariantsEquivOfConjugacy
    standardThreeTorusHomologyTwo.toIntLinearEquiv
    (circleMonodromyDifference orderThreeThreeTorusClutching 2).toIntLinearMap
    orderThreeDegreeTwoDifference
    (circleDifference_conjugacy orderThreeThreeTorusClutching 2
      standardThreeTorusHomologyTwo.toIntLinearEquiv
      orderThreeClutchingDegreeTwoMatrix.mulVecLin
      orderThreeThreeTorusClutching_homologyTwo)).trans
    orderThreeDegreeTwoCoinvariantsEquivInt

/-- The lower invariant of the order-three Wang sequence, in its positive integral coordinate. -/
public def orderThreeInvariantsEquivInt : OrderThreePresentation.Invariants ≃ₗ[ℤ] ℤ :=
  (invariantsEquivOfConjugacy
    standardThreeTorusHomologyOne.toIntLinearEquiv
    (circleMonodromyDifference orderThreeThreeTorusClutching 1).toIntLinearMap
    orderThreeDegreeOneDifference
    (circleDifference_conjugacy orderThreeThreeTorusClutching 1
      standardThreeTorusHomologyOne.toIntLinearEquiv
      orderThreeClutchingDegreeOneMatrix.mulVecLin
      orderThreeThreeTorusClutching_homologyOne)).trans
    orderThreeInvariantEquivInt

@[simp]
public theorem orderThreeCoinvariantsEquivInt_mk
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    orderThreeCoinvariantsEquivInt (Submodule.Quotient.mk x) =
      standardThreeTorusHomologyTwo x 0 := by
  unfold orderThreeCoinvariantsEquivInt
  change orderThreeDegreeTwoCoinvariantsEquivInt
    (Submodule.Quotient.mk (standardThreeTorusHomologyTwo x)) = _
  rw [orderThreeDegreeTwoCoinvariantsEquivInt_mk]

@[simp]
public theorem orderThreeInvariantsEquivInt_apply (x : OrderThreePresentation.Invariants) :
    orderThreeInvariantsEquivInt x = standardThreeTorusHomologyOne x.1 2 :=
  rfl

/-- The upper coinvariant of the order-four Wang sequence, in its positive integral coordinate. -/
public noncomputable def orderFourCoinvariantsEquivInt :
    OrderFourPresentation.Coinvariants ≃ₗ[ℤ] ℤ :=
  (coinvariantsEquivOfConjugacy
    standardThreeTorusHomologyTwo.toIntLinearEquiv
    (circleMonodromyDifference orderFourThreeTorusClutching 2).toIntLinearMap
    orderFourDegreeTwoDifference
    (circleDifference_conjugacy orderFourThreeTorusClutching 2
      standardThreeTorusHomologyTwo.toIntLinearEquiv
      orderFourClutchingDegreeTwoMatrix.mulVecLin
      orderFourThreeTorusClutching_homologyTwo)).trans
    orderFourDegreeTwoCoinvariantsEquivInt

/-- The lower invariant of the order-four Wang sequence, in its positive integral coordinate. -/
public def orderFourInvariantsEquivInt : OrderFourPresentation.Invariants ≃ₗ[ℤ] ℤ :=
  (invariantsEquivOfConjugacy
    standardThreeTorusHomologyOne.toIntLinearEquiv
    (circleMonodromyDifference orderFourThreeTorusClutching 1).toIntLinearMap
    orderFourDegreeOneDifference
    (circleDifference_conjugacy orderFourThreeTorusClutching 1
      standardThreeTorusHomologyOne.toIntLinearEquiv
      orderFourClutchingDegreeOneMatrix.mulVecLin
      orderFourThreeTorusClutching_homologyOne)).trans
    orderFourInvariantEquivInt

@[simp]
public theorem orderFourCoinvariantsEquivInt_mk
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    orderFourCoinvariantsEquivInt (Submodule.Quotient.mk x) =
      standardThreeTorusHomologyTwo x 0 := by
  unfold orderFourCoinvariantsEquivInt
  change orderFourDegreeTwoCoinvariantsEquivInt
    (Submodule.Quotient.mk (standardThreeTorusHomologyTwo x)) = _
  rw [orderFourDegreeTwoCoinvariantsEquivInt_mk]

@[simp]
public theorem orderFourInvariantsEquivInt_apply (x : OrderFourPresentation.Invariants) :
    orderFourInvariantsEquivInt x = standardThreeTorusHomologyOne x.1 2 :=
  rfl

/-- Negation as an integral linear equivalence. -/
public def intNegLinearEquiv : ℤ ≃ₗ[ℤ] ℤ where
  toFun x := -x
  invFun x := -x
  map_add' x y := neg_add x y
  map_smul' n x := by
    simp
  left_inv x := neg_neg x
  right_inv x := neg_neg x

/-- The order-three invariant coordinate with its orientation reversed. -/
public def orderThreeNegatedInvariantsEquivInt :
    OrderThreePresentation.Invariants ≃ₗ[ℤ] ℤ :=
  orderThreeInvariantsEquivInt.trans intNegLinearEquiv

@[simp]
public theorem orderThreeNegatedInvariantsEquivInt_apply
    (x : OrderThreePresentation.Invariants) :
    orderThreeNegatedInvariantsEquivInt x = -orderThreeInvariantsEquivInt x :=
  rfl

/-- Normalized coordinates on the second homology of the order-three mapping torus.

Coordinate zero is the invariant coordinate and coordinate one is the coinvariant coordinate.
-/
public noncomputable def orderThreeTotalAddEquiv
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeInvariantsEquivInt (OrderThreePresentation.totalToInvariants s) = 1) :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  rankOneTotalAddEquiv OrderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeInvariantsEquivInt s hs

/-- Normalized coordinates on the second homology of the order-four mapping torus.

Coordinate zero is the invariant coordinate and coordinate one is the coinvariant coordinate.
-/
public noncomputable def orderFourTotalAddEquiv
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching))
    (hs : orderFourInvariantsEquivInt (OrderFourPresentation.totalToInvariants s) = 1) :
    IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  rankOneTotalAddEquiv OrderFourPresentation orderFourCoinvariantsEquivInt
    orderFourInvariantsEquivInt s hs

/-- Order-three total coordinates using the reversed orientation of the invariant coordinate. -/
public noncomputable def orderThreeNegatedTotalAddEquiv
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeNegatedInvariantsEquivInt
      (OrderThreePresentation.totalToInvariants s) = 1) :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  rankOneTotalAddEquiv OrderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeNegatedInvariantsEquivInt s hs

@[simp]
public theorem orderThreeTotalAddEquiv_section
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeInvariantsEquivInt (OrderThreePresentation.totalToInvariants s) = 1) :
    orderThreeTotalAddEquiv s hs s = ![1, 0] :=
  rankOneTotalAddEquiv_apply_generator OrderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeInvariantsEquivInt s hs

@[simp]
public theorem orderFourTotalAddEquiv_section
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching))
    (hs : orderFourInvariantsEquivInt (OrderFourPresentation.totalToInvariants s) = 1) :
    orderFourTotalAddEquiv s hs s = ![1, 0] :=
  rankOneTotalAddEquiv_apply_generator OrderFourPresentation orderFourCoinvariantsEquivInt
    orderFourInvariantsEquivInt s hs

@[simp]
public theorem orderThreeNegatedTotalAddEquiv_section
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeNegatedInvariantsEquivInt
      (OrderThreePresentation.totalToInvariants s) = 1) :
    orderThreeNegatedTotalAddEquiv s hs s = ![1, 0] :=
  rankOneTotalAddEquiv_apply_generator OrderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeNegatedInvariantsEquivInt s hs

@[simp]
public theorem orderThreeTotalAddEquiv_fibreCoordinateZero
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeInvariantsEquivInt (OrderThreePresentation.totalToInvariants s) = 1) :
    orderThreeTotalAddEquiv s hs
        (OrderThreePresentation.inclusion
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      ![0, 1] := by
  rw [show OrderThreePresentation.inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) =
      OrderThreePresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) by rfl]
  change (rankOneTotalAddEquiv OrderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeInvariantsEquivInt s hs)
      (OrderThreePresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)))) = ![0, 1]
  rw [rankOneTotalAddEquiv_coinvariantsToTotal]
  funext i
  fin_cases i
  · rfl
  · change orderThreeCoinvariantsEquivInt
      (Submodule.Quotient.mk (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) = 1
    unfold orderThreeCoinvariantsEquivInt
    change orderThreeDegreeTwoCoinvariantsEquivInt
      (Submodule.Quotient.mk (standardThreeTorusHomologyTwo
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)))) = 1
    rw [standardThreeTorusHomologyTwo.apply_symm_apply,
      orderThreeDegreeTwoCoinvariantsEquivInt_mk]
    rfl

@[simp]
public theorem orderThreeNegatedTotalAddEquiv_fibreCoordinateZero
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeNegatedInvariantsEquivInt
      (OrderThreePresentation.totalToInvariants s) = 1) :
    orderThreeNegatedTotalAddEquiv s hs
        (OrderThreePresentation.inclusion
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      ![0, 1] := by
  rw [show OrderThreePresentation.inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) =
      OrderThreePresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) by rfl]
  change (rankOneTotalAddEquiv OrderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeNegatedInvariantsEquivInt s hs)
      (OrderThreePresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)))) = ![0, 1]
  rw [rankOneTotalAddEquiv_coinvariantsToTotal]
  funext i
  fin_cases i
  · rfl
  · change orderThreeCoinvariantsEquivInt
      (Submodule.Quotient.mk (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) = 1
    unfold orderThreeCoinvariantsEquivInt
    change orderThreeDegreeTwoCoinvariantsEquivInt
      (Submodule.Quotient.mk (standardThreeTorusHomologyTwo
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)))) = 1
    rw [standardThreeTorusHomologyTwo.apply_symm_apply,
      orderThreeDegreeTwoCoinvariantsEquivInt_mk]
    rfl

@[simp]
public theorem orderFourTotalAddEquiv_fibreCoordinateZero
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching))
    (hs : orderFourInvariantsEquivInt (OrderFourPresentation.totalToInvariants s) = 1) :
    orderFourTotalAddEquiv s hs
        (OrderFourPresentation.inclusion
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      ![0, 1] := by
  rw [show OrderFourPresentation.inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) =
      OrderFourPresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) by rfl]
  change (rankOneTotalAddEquiv OrderFourPresentation orderFourCoinvariantsEquivInt
    orderFourInvariantsEquivInt s hs)
      (OrderFourPresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)))) = ![0, 1]
  rw [rankOneTotalAddEquiv_coinvariantsToTotal]
  funext i
  fin_cases i
  · rfl
  · change orderFourCoinvariantsEquivInt
      (Submodule.Quotient.mk (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) = 1
    unfold orderFourCoinvariantsEquivInt
    change orderFourDegreeTwoCoinvariantsEquivInt
      (Submodule.Quotient.mk (standardThreeTorusHomologyTwo
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)))) = 1
    rw [standardThreeTorusHomologyTwo.apply_symm_apply,
      orderFourDegreeTwoCoinvariantsEquivInt_mk]
    rfl

end SphereSixComplex.Topology.EllipticThreeTorusRankOneMappingTorusCoordinates

end

end
