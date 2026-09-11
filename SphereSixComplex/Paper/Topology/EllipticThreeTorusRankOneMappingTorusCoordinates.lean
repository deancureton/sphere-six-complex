module

public import SphereSixComplex.Prerequisites.Topology.RankOneWangHomologySplitting
public import SphereSixComplex.Paper.Topology.EllipticThreeTorusWangEndpointCoordinates

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

public abbrev orderThreePresentation :=
  circleMappingTorusWangPresentationOfCover orderThreeThreeTorusClutching 1

public abbrev orderFourPresentation :=
  circleMappingTorusWangPresentationOfCover orderFourThreeTorusClutching 1

/-- The upper coinvariant of the order-three Wang sequence, in its positive integral coordinate. -/
public noncomputable def orderThreeCoinvariantsEquivInt :
    orderThreePresentation.Coinvariants ≃ₗ[ℤ] ℤ :=
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
public def orderThreeInvariantsEquivInt : orderThreePresentation.invariants ≃ₗ[ℤ] ℤ :=
  (invariantsEquivOfConjugacy
    standardThreeTorusHomologyOne.toIntLinearEquiv
    (circleMonodromyDifference orderThreeThreeTorusClutching 1).toIntLinearMap
    orderThreeDegreeOneDifference
    (circleDifference_conjugacy orderThreeThreeTorusClutching 1
      standardThreeTorusHomologyOne.toIntLinearEquiv
      orderThreeClutchingDegreeOneMatrix.mulVecLin
      orderThreeThreeTorusClutching_homologyOne)).trans
    orderThreeInvariantEquivInt



/-- The upper coinvariant of the order-four Wang sequence, in its positive integral coordinate. -/
public noncomputable def orderFourCoinvariantsEquivInt :
    orderFourPresentation.Coinvariants ≃ₗ[ℤ] ℤ :=
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
public def orderFourInvariantsEquivInt : orderFourPresentation.invariants ≃ₗ[ℤ] ℤ :=
  (invariantsEquivOfConjugacy
    standardThreeTorusHomologyOne.toIntLinearEquiv
    (circleMonodromyDifference orderFourThreeTorusClutching 1).toIntLinearMap
    orderFourDegreeOneDifference
    (circleDifference_conjugacy orderFourThreeTorusClutching 1
      standardThreeTorusHomologyOne.toIntLinearEquiv
      orderFourClutchingDegreeOneMatrix.mulVecLin
      orderFourThreeTorusClutching_homologyOne)).trans
    orderFourInvariantEquivInt



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
    orderThreePresentation.invariants ≃ₗ[ℤ] ℤ :=
  orderThreeInvariantsEquivInt.trans intNegLinearEquiv

@[simp]
public theorem orderThreeNegatedInvariantsEquivInt_apply
    (x : orderThreePresentation.invariants) :
    orderThreeNegatedInvariantsEquivInt x = -orderThreeInvariantsEquivInt x :=
  rfl

/-- Normalized coordinates on the second homology of the order-three mapping torus.

Coordinate zero is the invariant coordinate and coordinate one is the coinvariant coordinate.
-/
public noncomputable def orderThreeTotalAddEquiv
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeInvariantsEquivInt (orderThreePresentation.totalToInvariants s) = 1) :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  rankOneTotalAddEquiv orderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeInvariantsEquivInt s hs

/-- Normalized coordinates on the second homology of the order-four mapping torus.

Coordinate zero is the invariant coordinate and coordinate one is the coinvariant coordinate.
-/
public noncomputable def orderFourTotalAddEquiv
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching))
    (hs : orderFourInvariantsEquivInt (orderFourPresentation.totalToInvariants s) = 1) :
    IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  rankOneTotalAddEquiv orderFourPresentation orderFourCoinvariantsEquivInt
    orderFourInvariantsEquivInt s hs

/-- Order-three total coordinates using the reversed orientation of the invariant coordinate. -/
public noncomputable def orderThreeNegatedTotalAddEquiv
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeNegatedInvariantsEquivInt
      (orderThreePresentation.totalToInvariants s) = 1) :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  rankOneTotalAddEquiv orderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeNegatedInvariantsEquivInt s hs


@[simp]
public theorem orderFourTotalAddEquiv_section
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching))
    (hs : orderFourInvariantsEquivInt (orderFourPresentation.totalToInvariants s) = 1) :
    orderFourTotalAddEquiv s hs s = ![1, 0] :=
  rankOneTotalAddEquiv_apply_generator orderFourPresentation orderFourCoinvariantsEquivInt
    orderFourInvariantsEquivInt s hs

@[simp]
public theorem orderThreeNegatedTotalAddEquiv_section
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeNegatedInvariantsEquivInt
      (orderThreePresentation.totalToInvariants s) = 1) :
    orderThreeNegatedTotalAddEquiv s hs s = ![1, 0] :=
  rankOneTotalAddEquiv_apply_generator orderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeNegatedInvariantsEquivInt s hs


@[simp]
public theorem orderThreeNegatedTotalAddEquiv_fiberCoordinateZero
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching))
    (hs : orderThreeNegatedInvariantsEquivInt
      (orderThreePresentation.totalToInvariants s) = 1) :
    orderThreeNegatedTotalAddEquiv s hs
        (orderThreePresentation.inclusion
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      ![0, 1] := by
  rw [show orderThreePresentation.inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) =
      orderThreePresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) by rfl]
  change (rankOneTotalAddEquiv orderThreePresentation orderThreeCoinvariantsEquivInt
    orderThreeNegatedInvariantsEquivInt s hs)
      (orderThreePresentation.coinvariantsToTotal
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
public theorem orderFourTotalAddEquiv_fiberCoordinateZero
    (s : IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching))
    (hs : orderFourInvariantsEquivInt (orderFourPresentation.totalToInvariants s) = 1) :
    orderFourTotalAddEquiv s hs
        (orderFourPresentation.inclusion
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      ![0, 1] := by
  rw [show orderFourPresentation.inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) =
      orderFourPresentation.coinvariantsToTotal
        (Submodule.Quotient.mk
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) by rfl]
  change (rankOneTotalAddEquiv orderFourPresentation orderFourCoinvariantsEquivInt
    orderFourInvariantsEquivInt s hs)
      (orderFourPresentation.coinvariantsToTotal
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
