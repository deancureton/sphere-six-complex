module

public import SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
public import SphereSixComplex.Topology.PaperPropositionSevenFourteenDegreeTwoAlgebra

/-!
# Degree-two comparison for the finite cyclic elliptic quotients

Mathlib currently has no Cartan--Leray spectral sequence or transfer construction identifying
the integral homology of a finite cyclic quotient.  This file isolates the exact perfect-pairing
conclusion needed in Section 7.  It also proves that the pullback classes computed in Proposition
7.14 force the displayed order-three and order-four covering matrices.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex.Topology.PaperFiniteCyclicQuotientDegreeTwoComparison

open Geometry Geometry.AnalyticTorusFamily Geometry.EllipticFamilySpecialization
open Geometry.GlobalTorusFamily
open PaperEllipticFillingRadialRetraction PaperEllipticReducedCentralFiberCoverModels
open PaperPropositionSevenFourteenDegreeTwoAlgebra

/-- Evaluation of a degree-two covector in the standard exterior-square coordinates. -/
public def degreeTwoEvaluation (a x : DegreeTwoLattice) : ℤ :=
  dotProduct a x

/-- Simultaneous evaluation against a finite family of degree-two pullback classes. -/
public def degreeTwoEvaluationMap {r : ℕ} (pullbackBasis : Fin r → DegreeTwoLattice) :
    DegreeTwoLattice →+ (Fin r → ℤ) where
  toFun x i := degreeTwoEvaluation (pullbackBasis i) x
  map_zero' := by
    funext i
    simp [degreeTwoEvaluation]
  map_add' x y := by
    funext i
    simp [degreeTwoEvaluation, dotProduct_add]

/-- The perfect-pairing conclusion needed from a finite cyclic quotient calculation.

The quotient basis is dual to the displayed pullback classes, and the projection map is
evaluation against those classes.  For the elliptic quotients below, a transfer or
Cartan--Leray argument must construct this datum. -/
public structure DegreeTwoPullbackRealization
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (projection : C(E, X)) (sourceBasis : IntegralSingularHomology 2 E ≃+ DegreeTwoLattice)
    {r : ℕ} (pullbackBasis : Fin r → DegreeTwoLattice) where
  quotientBasis : IntegralSingularHomology 2 X ≃+ (Fin r → ℤ)
  projection_coordinates : ∀ x,
    quotientBasis (integralSingularHomologyMap 2 projection x) =
      degreeTwoEvaluationMap pullbackBasis (sourceBasis x)

namespace DegreeTwoPullbackRealization

variable {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
  {projection : C(E, X)} {sourceBasis : IntegralSingularHomology 2 E ≃+ DegreeTwoLattice}
  {r : ℕ} {pullbackBasis : Fin r → DegreeTwoLattice}

/-- Conjugating the covering projection by the selected bases gives evaluation. -/
public theorem projection_conjugacy_apply
    (R : DegreeTwoPullbackRealization projection sourceBasis pullbackBasis)
    (x : DegreeTwoLattice) :
    R.quotientBasis
        (integralSingularHomologyMap 2 projection (sourceBasis.symm x)) =
      degreeTwoEvaluationMap pullbackBasis x := by
  simpa using R.projection_coordinates (sourceBasis.symm x)

end DegreeTwoPullbackRealization

/-- The two order-three pullback classes used in the paper's degree-two matrix. -/
public def orderThreePullbackInvariantZero : OrderThreeDegreeTwoInvariants :=
  ⟨1 • gammaEpsilonOne + 0 • qClass, orderThree_combination_fixed 1 0⟩

public def orderThreePullbackInvariantOne : OrderThreeDegreeTwoInvariants :=
  ⟨(-2 : ℤ) • gammaEpsilonOne + 1 • qClass, orderThree_combination_fixed (-2) 1⟩

public def orderThreePullbackClasses :
    Fin 2 → orderThreeDegreeTwoPullbackCandidate :=
  ![⟨orderThreePullbackInvariantZero, Submodule.mem_top⟩,
    ⟨orderThreePullbackInvariantOne, Submodule.mem_top⟩]

/-- The two order-four pullback classes form the parity sublattice from Proposition 7.14. -/
public def orderFourPullbackInvariantZero : OrderFourDegreeTwoInvariants :=
  ⟨2 • gammaEpsilonTwo + 0 • qClass, orderFour_combination_fixed 2 0⟩

public def orderFourPullbackInvariantOne : OrderFourDegreeTwoInvariants :=
  ⟨(-3 : ℤ) • gammaEpsilonTwo + 1 • qClass, orderFour_combination_fixed (-3) 1⟩

public theorem orderFourPullbackInvariantZero_mem :
    orderFourPullbackInvariantZero ∈ orderFourDegreeTwoPullbackCandidate := by
  rw [mem_orderFourDegreeTwoPullbackCandidate_iff]
  change ((2 : ℤ) : ZMod 2) = 0
  decide

public theorem orderFourPullbackInvariantOne_mem :
    orderFourPullbackInvariantOne ∈ orderFourDegreeTwoPullbackCandidate := by
  rw [mem_orderFourDegreeTwoPullbackCandidate_iff]
  change ((-3 : ℤ) : ZMod 2) = 1
  decide

public def orderFourPullbackClasses :
    Fin 2 → orderFourDegreeTwoPullbackCandidate :=
  ![⟨orderFourPullbackInvariantZero, orderFourPullbackInvariantZero_mem⟩,
    ⟨orderFourPullbackInvariantOne, orderFourPullbackInvariantOne_mem⟩]

/-- The order-three pullback classes as covectors on the covering torus. -/
public def orderThreePullbackBasis : Fin 2 → DegreeTwoLattice :=
  fun i ↦ (orderThreePullbackClasses i).1.1

/-- The order-four pullback classes as covectors on the covering torus. -/
public def orderFourPullbackBasis : Fin 2 → DegreeTwoLattice :=
  fun i ↦ (orderFourPullbackClasses i).1.1

/-- Evaluation against the order-three pullback basis gives the first two rows of `alphaTwo`. -/
public theorem orderThreeEvaluation_eq_alphaTwoRows (x : DegreeTwoLattice) :
    degreeTwoEvaluationMap orderThreePullbackBasis x =
      ![(SphereSixComplex.alphaTwoMatrix *ᵥ x) 0,
        (SphereSixComplex.alphaTwoMatrix *ᵥ x) 1] := by
  funext i
  fin_cases i <;>
    simp [degreeTwoEvaluationMap, degreeTwoEvaluation, orderThreePullbackBasis,
      orderThreePullbackClasses, orderThreePullbackInvariantZero,
      orderThreePullbackInvariantOne, gammaEpsilonOne, qClass,
      SphereSixComplex.alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Evaluation against the order-four pullback basis is the negative of the last two rows of
`alphaTwo`; the signs are exactly the right-hand Mayer--Vietoris convention. -/
public theorem orderFourEvaluation_eq_negAlphaTwoRows (x : DegreeTwoLattice) :
    degreeTwoEvaluationMap orderFourPullbackBasis x =
      ![-(SphereSixComplex.alphaTwoMatrix *ᵥ x) 2,
        -(SphereSixComplex.alphaTwoMatrix *ᵥ x) 3] := by
  funext i
  fin_cases i <;>
    simp [degreeTwoEvaluationMap, degreeTwoEvaluation, orderFourPullbackBasis,
      orderFourPullbackClasses, orderFourPullbackInvariantZero,
      orderFourPullbackInvariantOne, gammaEpsilonTwo, qClass,
      SphereSixComplex.alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

/-- Exact remaining transfer/perfect-pairing theorem for the order-three reduced central fibre. -/
public abbrev OrderThreeReducedCentralFiberDegreeTwoRealization :=
  DegreeTwoPullbackRealization
    (RadialEllipticActionData.centralFiberCoverProjection (orderThreeRadialActionData F))
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo
    orderThreePullbackBasis

/-- Exact remaining transfer/perfect-pairing theorem for the order-four reduced central fibre. -/
public abbrev OrderFourReducedCentralFiberDegreeTwoRealization :=
  DegreeTwoPullbackRealization
    (RadialEllipticActionData.centralFiberCoverProjection (orderFourRadialActionData F))
    (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo
    orderFourPullbackBasis

/-- An order-three realization supplies the required rank-two basis and covering matrix. -/
public theorem orderThree_projection_coordinates
    (R : OrderThreeReducedCentralFiberDegreeTwoRealization F) (x : DegreeTwoLattice) :
    R.quotientBasis
        (orderThreeReducedCentralFiberCoverHomologyDegreeTwo F x) =
      ![(SphereSixComplex.alphaTwoMatrix *ᵥ x) 0,
        (SphereSixComplex.alphaTwoMatrix *ᵥ x) 1] := by
  calc
    R.quotientBasis (orderThreeReducedCentralFiberCoverHomologyDegreeTwo F x) =
        degreeTwoEvaluationMap orderThreePullbackBasis x := by
      change R.quotientBasis
          (integralSingularHomologyMap 2
            (RadialEllipticActionData.centralFiberCoverProjection
              (orderThreeRadialActionData F))
            ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) = _
      rw [R.projection_coordinates, AddEquiv.apply_symm_apply]
    _ = _ := orderThreeEvaluation_eq_alphaTwoRows x

/-- An order-four realization supplies the required rank-two basis and covering matrix. -/
public theorem orderFour_projection_coordinates
    (R : OrderFourReducedCentralFiberDegreeTwoRealization F) (x : DegreeTwoLattice) :
    R.quotientBasis
        (orderFourReducedCentralFiberCoverHomologyDegreeTwo F x) =
      ![-(SphereSixComplex.alphaTwoMatrix *ᵥ x) 2,
        -(SphereSixComplex.alphaTwoMatrix *ᵥ x) 3] := by
  calc
    R.quotientBasis (orderFourReducedCentralFiberCoverHomologyDegreeTwo F x) =
        degreeTwoEvaluationMap orderFourPullbackBasis x := by
      change R.quotientBasis
          (integralSingularHomologyMap 2
            (RadialEllipticActionData.centralFiberCoverProjection
              (orderFourRadialActionData F))
            ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) = _
      rw [R.projection_coordinates, AddEquiv.apply_symm_apply]
    _ = _ := orderFourEvaluation_eq_negAlphaTwoRows x

end SphereSixComplex.Topology.PaperFiniteCyclicQuotientDegreeTwoComparison
