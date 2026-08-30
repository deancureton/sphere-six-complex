module

public import SphereSixComplex.Topology.AffineCyclicCoverDegreeTwoInvariance

/-!
# Degree-two coinvariants for the elliptic finite covers

This scratch module computes the integral coinvariants of the two exterior-square deck actions.
It is deliberately not imported by the production development yet.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology.EllipticDegreeTwoCoinvariants

open LatticeData TriangleGroup
open Topology.PaperFiniteCyclicQuotientDegreeTwoComparison
open Topology.PaperLemmaSevenThirteenAlgebra
open Topology.PaperPropositionSevenFourteenDegreeTwoAlgebra

/-- The order-three exterior-square deck difference. -/
public def orderThreeDeckDifference : DegreeTwoLattice →ₗ[ℤ] DegreeTwoLattice :=
  (exteriorSquareMap (rhoLambda g₁)).toIntLinearMap - LinearMap.id

/-- The order-four exterior-square deck difference. -/
public def orderFourDeckDifference : DegreeTwoLattice →ₗ[ℤ] DegreeTwoLattice :=
  (exteriorSquareMap (rhoLambda g₂)).toIntLinearMap - LinearMap.id

/-- Free coordinates on the order-three deck coinvariants. -/
public def orderThreeCoinvariantCoordinates : DegreeTwoLattice →ₗ[ℤ] IntSquared where
  toFun x := ![2 * x 0 + x 1 + 3 * x 2, 6 * x 2 + x 3]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    all_goals ring

/-- Free coordinates on the order-four deck coinvariants. -/
public def orderFourCoinvariantCoordinates : DegreeTwoLattice →ₗ[ℤ] IntSquared where
  toFun x := ![x 0 + x 1 + 2 * x 2, 6 * x 2 + x 3]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    all_goals ring

public theorem orderThreeDeckDifference_apply (x : DegreeTwoLattice) :
    orderThreeDeckDifference x =
      ![-x 0 + x 1,
        -x 0 - 2 * x 1,
        x 0,
        -6 * x 0,
        6 * x 0 + 2 * x 1 + 6 * x 2 - x 3 - x 4 + x 5,
        -8 * x 0 - 2 * x 1 - 6 * x 2 + x 3 - x 4 - 2 * x 5] := by
  funext i
  fin_cases i <;>
    simp [orderThreeDeckDifference, exteriorSquareMap, exteriorSquareMatrix,
      secondCompoundMatrix, A₁, periodPairFirst, periodPairSecond, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Pi.single_apply] <;> ring

public theorem orderFourDeckDifference_apply (x : DegreeTwoLattice) :
    orderFourDeckDifference x =
      ![-x 0 - x 1,
        x 0 - x 1,
        x 1,
        -6 * x 1,
        3 * x 1 - x 4 - x 5,
        -3 * x 0 - 6 * x 1 - 6 * x 2 + x 3 + x 4 - x 5] := by
  funext i
  fin_cases i <;>
    simp [orderFourDeckDifference, exteriorSquareMap, exteriorSquareMatrix,
      secondCompoundMatrix, A₂, periodPairFirst, periodPairSecond, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Pi.single_apply] <;> ring

public theorem orderThreeCoinvariantCoordinates_difference (x : DegreeTwoLattice) :
    orderThreeCoinvariantCoordinates (orderThreeDeckDifference x) = 0 := by
  rw [orderThreeDeckDifference_apply]
  funext i
  fin_cases i <;> simp [orderThreeCoinvariantCoordinates]
  all_goals ring

public theorem orderFourCoinvariantCoordinates_difference (x : DegreeTwoLattice) :
    orderFourCoinvariantCoordinates (orderFourDeckDifference x) = 0 := by
  rw [orderFourDeckDifference_apply]
  funext i
  fin_cases i <;> simp [orderFourCoinvariantCoordinates]
  all_goals ring

private def orderThreeRangePreimage (x : DegreeTwoLattice) : DegreeTwoLattice :=
  ![x 2, x 0 + x 2, 0, 2 * x 0 + 6 * x 2 - 2 * x 4 - x 5,
    0, -2 * x 2 - x 4 - x 5]

private def orderFourRangePreimage (x : DegreeTwoLattice) : DegreeTwoLattice :=
  ![x 1 + x 2, x 2, 0, x 4 + x 5 + 3 * x 1 + 6 * x 2, 3 * x 2 - x 4, 0]

private theorem orderThreeDeckDifference_rangePreimage (x : DegreeTwoLattice)
    (hx : orderThreeCoinvariantCoordinates x = 0) :
    orderThreeDeckDifference (orderThreeRangePreimage x) = x := by
  rw [orderThreeDeckDifference_apply]
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [orderThreeCoinvariantCoordinates] at h0 h1
  funext i
  fin_cases i <;> simp [orderThreeRangePreimage] <;> omega

private theorem orderFourDeckDifference_rangePreimage (x : DegreeTwoLattice)
    (hx : orderFourCoinvariantCoordinates x = 0) :
    orderFourDeckDifference (orderFourRangePreimage x) = x := by
  rw [orderFourDeckDifference_apply]
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [orderFourCoinvariantCoordinates] at h0 h1
  funext i
  fin_cases i <;> simp [orderFourRangePreimage] <;> omega

/-- The order-three deck-difference range is exactly the kernel of the displayed coordinates. -/
public theorem orderThreeDeckDifference_range_eq_ker :
    LinearMap.range orderThreeDeckDifference =
      LinearMap.ker orderThreeCoinvariantCoordinates := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (orderThreeCoinvariantCoordinates_difference y)
  · intro hx
    exact ⟨orderThreeRangePreimage x,
      orderThreeDeckDifference_rangePreimage x (LinearMap.mem_ker.mp hx)⟩

/-- The order-four deck-difference range is exactly the kernel of the displayed coordinates. -/
public theorem orderFourDeckDifference_range_eq_ker :
    LinearMap.range orderFourDeckDifference =
      LinearMap.ker orderFourCoinvariantCoordinates := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (orderFourCoinvariantCoordinates_difference y)
  · intro hx
    exact ⟨orderFourRangePreimage x,
      orderFourDeckDifference_rangePreimage x (LinearMap.mem_ker.mp hx)⟩

public theorem orderThreeCoinvariantCoordinates_surjective :
    Function.Surjective orderThreeCoinvariantCoordinates := by
  intro y
  refine ⟨![0, y 0, 0, y 1, 0, 0], ?_⟩
  funext i
  fin_cases i <;> simp [orderThreeCoinvariantCoordinates]

public theorem orderFourCoinvariantCoordinates_surjective :
    Function.Surjective orderFourCoinvariantCoordinates := by
  intro y
  refine ⟨![y 0, 0, 0, y 1, 0, 0], ?_⟩
  funext i
  fin_cases i <;> simp [orderFourCoinvariantCoordinates]

public abbrev OrderThreeDegreeTwoCoinvariants :=
  DegreeTwoLattice ⧸ LinearMap.range orderThreeDeckDifference

public abbrev OrderFourDegreeTwoCoinvariants :=
  DegreeTwoLattice ⧸ LinearMap.range orderFourDeckDifference

/-- The order-three degree-two deck coinvariants are free of rank two. -/
public noncomputable def orderThreeCoinvariantsEquivIntSquared :
    OrderThreeDegreeTwoCoinvariants ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ orderThreeDeckDifference_range_eq_ker).trans
    (orderThreeCoinvariantCoordinates.quotKerEquivOfSurjective
      orderThreeCoinvariantCoordinates_surjective)

/-- The order-four degree-two deck coinvariants are free of rank two. -/
public noncomputable def orderFourCoinvariantsEquivIntSquared :
    OrderFourDegreeTwoCoinvariants ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ orderFourDeckDifference_range_eq_ker).trans
    (orderFourCoinvariantCoordinates.quotKerEquivOfSurjective
      orderFourCoinvariantCoordinates_surjective)

@[simp] public theorem orderThreeCoinvariantsEquivIntSquared_mk (x : DegreeTwoLattice) :
    orderThreeCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      orderThreeCoinvariantCoordinates x := by
  rfl

@[simp] public theorem orderFourCoinvariantsEquivIntSquared_mk (x : DegreeTwoLattice) :
    orderFourCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      orderFourCoinvariantCoordinates x := by
  rfl

/-- Coordinates of the order-three covering map on deck coinvariants. -/
public def orderThreeCoverCoordinates : IntSquared →ₗ[ℤ] IntSquared where
  toFun x := ![x 0, x 1 - 2 * x 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    ring

/-- Coordinates of the order-four covering map on deck coinvariants. -/
public def orderFourCoverCoordinates : IntSquared →ₗ[ℤ] IntSquared where
  toFun x := ![2 * x 0, x 1 - 3 * x 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
    all_goals ring

/-- The order-three pullback evaluations factor through the free deck coinvariants. -/
public theorem orderThreeEvaluation_eq_coverCoordinates (x : DegreeTwoLattice) :
    degreeTwoEvaluationMap orderThreePullbackBasis x =
      orderThreeCoverCoordinates (orderThreeCoinvariantCoordinates x) := by
  funext i
  fin_cases i <;>
    simp [degreeTwoEvaluationMap, degreeTwoEvaluation, orderThreePullbackBasis,
      orderThreePullbackClasses, orderThreePullbackInvariantZero,
      orderThreePullbackInvariantOne, orderThreeCoinvariantCoordinates,
      orderThreeCoverCoordinates, gammaEpsilonOne, qClass, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The order-four pullback evaluations factor through the free deck coinvariants with index two. -/
public theorem orderFourEvaluation_eq_coverCoordinates (x : DegreeTwoLattice) :
    degreeTwoEvaluationMap orderFourPullbackBasis x =
      orderFourCoverCoordinates (orderFourCoinvariantCoordinates x) := by
  funext i
  fin_cases i <;>
    simp [degreeTwoEvaluationMap, degreeTwoEvaluation, orderFourPullbackBasis,
      orderFourPullbackClasses, orderFourPullbackInvariantZero,
      orderFourPullbackInvariantOne, orderFourCoinvariantCoordinates,
      orderFourCoverCoordinates, gammaEpsilonTwo, qClass, dotProduct, Fin.sum_univ_succ] <;>
    ring

end SphereSixComplex.Topology.EllipticDegreeTwoCoinvariants
