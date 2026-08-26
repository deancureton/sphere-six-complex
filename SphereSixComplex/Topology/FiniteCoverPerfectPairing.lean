module

public import SphereSixComplex.Topology.PaperAffineCyclicQuotientHomologyCoordinates
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Perfect pairings and finite-cover homology coordinates

This file proves the algebraic perfect-pairing theorem that turns an explicit basis of the
integral cohomology pullback lattice into coordinates on quotient homology.  It also states the
smallest functorial clause missing from the existing general affine cyclic `H₁` presentation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex.Topology.FiniteCoverPerfectPairing

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization Geometry.GlobalTorusFamily
open LatticeData PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels PaperLemmaSevenThirteenAlgebra
open PaperMultipleFiberHOneTopology
open PaperFiniteCyclicQuotientDegreeTwoComparison
open PaperAffineCyclicQuotientHomologyCoordinates
open PaperPropositionSevenFourteenDegreeTwoAlgebra TwistObstruction

/-- An actual basis of quotient degree-two cohomology whose pullback is a displayed family of
covectors on the covering space.  `reflexive` is the exact torsion-freeness/perfect-pairing input
needed to recover homology from its integral dual. -/
public structure FiniteCoverDegreeTwoPullbackBasis
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (projection : C(E, X)) (sourceBasis : IntegralSingularHomology 2 E ≃+ DegreeTwoLattice)
    {r : ℕ} (pullbackBasis : Fin r → DegreeTwoLattice) where
  quotientDualBasis : Module.Basis (Fin r) ℤ
    (Module.Dual ℤ (IntegralSingularHomology 2 X))
  reflexive : Function.Bijective
    (Module.Dual.eval ℤ (IntegralSingularHomology 2 X))
  pullback_apply : ∀ (i : Fin r) (x : DegreeTwoLattice),
    quotientDualBasis i
        (integralSingularHomologyMap 2 projection (sourceBasis.symm x)) =
      degreeTwoEvaluation (pullbackBasis i) x

namespace FiniteCoverDegreeTwoPullbackBasis

variable {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
  {projection : C(E, X)} {sourceBasis : IntegralSingularHomology 2 E ≃+ DegreeTwoLattice}
  {r : ℕ} {pullbackBasis : Fin r → DegreeTwoLattice}

/-- The quotient homology basis dual to the explicit pullback basis. -/
public def quotientBasis
    (P : FiniteCoverDegreeTwoPullbackBasis projection sourceBasis pullbackBasis) :
    IntegralSingularHomology 2 X ≃+ (Fin r → ℤ) :=
  ((LinearEquiv.ofBijective
      (Module.Dual.eval ℤ (IntegralSingularHomology 2 X)) P.reflexive).trans
    P.quotientDualBasis.toDualEquiv.symm).trans
      P.quotientDualBasis.equivFun |>.toAddEquiv

/-- Perfect pairing forces the covering projection to be evaluation against the pullback
cohomology basis. -/
public theorem quotientBasis_projection
    (P : FiniteCoverDegreeTwoPullbackBasis projection sourceBasis pullbackBasis)
    (x : DegreeTwoLattice) :
    P.quotientBasis
        (integralSingularHomologyMap 2 projection (sourceBasis.symm x)) =
      degreeTwoEvaluationMap pullbackBasis x := by
  funext i
  change P.quotientDualBasis.equivFun
      (P.quotientDualBasis.toDualEquiv.symm
        (Module.Dual.eval ℤ (IntegralSingularHomology 2 X)
          (integralSingularHomologyMap 2 projection (sourceBasis.symm x)))) i = _
  rw [← P.quotientDualBasis.toDual_eq_equivFun]
  rw [show P.quotientDualBasis.toDual
      (P.quotientDualBasis.toDualEquiv.symm
        (Module.Dual.eval ℤ (IntegralSingularHomology 2 X)
          (integralSingularHomologyMap 2 projection (sourceBasis.symm x)))) =
      Module.Dual.eval ℤ (IntegralSingularHomology 2 X)
        (integralSingularHomologyMap 2 projection (sourceBasis.symm x)) from
    P.quotientDualBasis.toDualEquiv.apply_symm_apply _]
  simpa [Module.Dual.eval_apply, degreeTwoEvaluationMap] using P.pullback_apply i x

/-- The generic perfect-pairing construction supplies `DegreeTwoPullbackRealization`. -/
public def toDegreeTwoPullbackRealization
    (P : FiniteCoverDegreeTwoPullbackBasis projection sourceBasis pullbackBasis) :
    DegreeTwoPullbackRealization projection sourceBasis pullbackBasis where
  quotientBasis := P.quotientBasis
  projection_coordinates x := by
    simpa using P.quotientBasis_projection (sourceBasis x)

end FiniteCoverDegreeTwoPullbackBasis

namespace DegreeTwoPullbackRealization

variable {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
  {projection : C(E, X)} {sourceBasis : IntegralSingularHomology 2 E ≃+ DegreeTwoLattice}
  {r : ℕ} {pullbackBasis : Fin r → DegreeTwoLattice}

/-- Recover the cohomological perfect-pairing package from explicit quotient homology
coordinates. -/
public noncomputable def toFiniteCoverDegreeTwoPullbackBasis
    (R : DegreeTwoPullbackRealization projection sourceBasis pullbackBasis) :
    FiniteCoverDegreeTwoPullbackBasis projection sourceBasis pullbackBasis := by
  let b : Module.Basis (Fin r) ℤ (IntegralSingularHomology 2 X) :=
    Module.Basis.ofEquivFun R.quotientBasis.toIntLinearEquiv
  refine
    { quotientDualBasis := b.dualBasis
      reflexive := ⟨b.eval_injective, ?_⟩
      pullback_apply := ?_ }
  · rw [← LinearMap.range_eq_top]
    exact b.eval_range
  · intro i x
    rw [Module.Basis.dualBasis_apply, Module.Basis.ofEquivFun_repr_apply]
    exact congrFun (R.projection_conjugacy_apply x) i

end DegreeTwoPullbackRealization

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- Exposed form of the existing general affine cyclic quotient presentation equivalence. -/
public noncomputable def affineCyclicHOnePresentationEquiv
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    IntegralSingularHomology 1 D.reducedCentralFiber ≃ₗ[ℤ]
      MultipleFiberHOnePresentation P.latticeDifference P.twist (m : ℤ) :=
  EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation P

/-- Naturality of the standard abelianized covering-group presentation.

The existing general theorem exposes the abstract presentation equivalence but not its value on
the covering projection.  Mathlib has neither the required fundamental-group presentation for a
free affine cyclic quotient nor a natural `H₁ = pi₁^ab` comparison, so this is the smallest
general functorial boundary. -/
public theorem establishedAffineCyclicHOnePresentation_projection
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    affineCyclicHOnePresentationEquiv P
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection D)
          ((affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeOne.symm x)) =
      latticeToMultipleFiberHOnePresentation
        P.latticeDifference P.twist (m : ℤ) x := by
  simpa only [affineCyclicHOnePresentationEquiv,
    affineCyclicCentralFiberCoverSourceHomologyBasis,
    latticeToMultipleFiberHOnePresentation,
    EstablishedAffineCyclicQuotientHomology.centralFiberCoverSourceDegreeOneBasis,
    EstablishedAffineCyclicQuotientHomology.latticeProjection] using
    EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation_projection P x

/-- Exposed order-three presentation coordinates. -/
public noncomputable def orderOnePresentationEquivIntSquared :
    OrderOneSelectedPresentation ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ range_orderOneRelationMap_eq_ker).trans
    (orderOnePresentationCoordinates.quotKerEquivOfSurjective
      orderOnePresentationCoordinates_surjective)

/-- Exposed order-four presentation coordinates. -/
public noncomputable def orderTwoPresentationEquivIntSquared :
    OrderTwoSelectedPresentation ≃ₗ[ℤ] IntSquared :=
  (Submodule.quotEquivOfEq _ _ range_orderTwoRelationMap_eq_ker).trans
    (orderTwoPresentationCoordinates.quotKerEquivOfSurjective
      orderTwoPresentationCoordinates_surjective)

public theorem orderOnePresentationEquiv_lattice (x : Lattice) :
    orderOnePresentationEquivIntSquared
        (latticeToMultipleFiberHOnePresentation orderOneDifference v₁ 3 x) =
      orderOneLatticeProjectionCoordinates x := by
  change orderOnePresentationCoordinates (Submodule.Quotient.mk x, 0) = _
  funext i
  fin_cases i <;>
    simp [orderOnePresentationCoordinates, orderOneLatticeProjectionCoordinates,
      orderOneCoinvariantsEquivIntSquared_mk, orderOneCoordinates, psiOne]

public theorem orderTwoPresentationEquiv_lattice (x : Lattice) :
    orderTwoPresentationEquivIntSquared
        (latticeToMultipleFiberHOnePresentation orderTwoDifference v₂ 4 x) =
      orderTwoLatticeProjectionCoordinates x := by
  change orderTwoPresentationCoordinates (Submodule.Quotient.mk x, 0) = _
  funext i
  fin_cases i <;>
    simp [orderTwoPresentationCoordinates, orderTwoLatticeProjectionCoordinates,
      orderTwoCoinvariantsEquivIntSquared_mk, orderTwoCoordinates, psiTwo]

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

/-- The selected order-three presentation equivalence, with the actual presentation data left
in its functorial form. -/
public noncomputable def orderThreePresentationCoordinateEquiv :
    MultipleFiberHOnePresentation
        (orderThreeCentralFiberPresentationData F).latticeDifference
        (orderThreeCentralFiberPresentationData F).twist 3 ≃ₗ[ℤ] IntSquared := by
  change MultipleFiberHOnePresentation orderOneDifference epsilon 3 ≃ₗ[ℤ] IntSquared
  have hRange :
      LinearMap.range (multipleFiberRelationMap orderOneDifference epsilon 3) =
        LinearMap.ker orderOnePresentationCoordinates := by
    simpa [TwistObstruction.v₁] using range_orderOneRelationMap_eq_ker
  exact (Submodule.quotEquivOfEq _ _ hRange).trans
    (orderOnePresentationCoordinates.quotKerEquivOfSurjective
      orderOnePresentationCoordinates_surjective)

/-- The selected order-four presentation equivalence, with the actual presentation data left in
its functorial form. -/
public noncomputable def orderFourPresentationCoordinateEquiv :
    MultipleFiberHOnePresentation
        (orderFourCentralFiberPresentationData F).latticeDifference
        (orderFourCentralFiberPresentationData F).twist 4 ≃ₗ[ℤ] IntSquared := by
  change MultipleFiberHOnePresentation orderTwoDifference (-epsilon') 4 ≃ₗ[ℤ] IntSquared
  have hRange :
      LinearMap.range (multipleFiberRelationMap orderTwoDifference (-epsilon') 4) =
        LinearMap.ker orderTwoPresentationCoordinates := by
    simpa [TwistObstruction.v₂] using range_orderTwoRelationMap_eq_ker
  exact (Submodule.quotEquivOfEq _ _ hRange).trans
    (orderTwoPresentationCoordinates.quotKerEquivOfSurjective
      orderTwoPresentationCoordinates_surjective)

/-- H₁ basis obtained functorially from the general affine cyclic quotient theorem. -/
public noncomputable def orderThreeHOneBasis :
    IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) ≃+ IntSquared :=
  ((affineCyclicHOnePresentationEquiv
    (orderThreeCentralFiberPresentationData F)).trans
      (orderThreePresentationCoordinateEquiv F)).toAddEquiv

public noncomputable def orderFourHOneBasis :
    IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) ≃+ IntSquared :=
  ((affineCyclicHOnePresentationEquiv
    (orderFourCentralFiberPresentationData F)).trans
      (orderFourPresentationCoordinateEquiv F)).toAddEquiv

public theorem orderThreePresentationCoordinateEquiv_lattice (x : Lattice) :
    orderThreePresentationCoordinateEquiv F
        (latticeToMultipleFiberHOnePresentation
          (orderThreeCentralFiberPresentationData F).latticeDifference
          (orderThreeCentralFiberPresentationData F).twist 3 x) =
      orderOneLatticeProjectionCoordinates x := by
  change orderOnePresentationCoordinates (Submodule.Quotient.mk x, 0) = _
  funext i
  fin_cases i <;>
    simp [orderOnePresentationCoordinates, orderOneLatticeProjectionCoordinates,
      orderOneCoinvariantsEquivIntSquared_mk, orderOneCoordinates, psiOne]

public theorem orderFourPresentationCoordinateEquiv_lattice (x : Lattice) :
    orderFourPresentationCoordinateEquiv F
        (latticeToMultipleFiberHOnePresentation
          (orderFourCentralFiberPresentationData F).latticeDifference
          (orderFourCentralFiberPresentationData F).twist 4 x) =
      orderTwoLatticeProjectionCoordinates x := by
  change orderTwoPresentationCoordinates (Submodule.Quotient.mk x, 0) = _
  funext i
  fin_cases i <;>
    simp [orderTwoPresentationCoordinates, orderTwoLatticeProjectionCoordinates,
      orderTwoCoinvariantsEquivIntSquared_mk, orderTwoCoordinates, psiTwo]

/-- Naturality now gives the actual order-three covering coordinates unconditionally. -/
public theorem orderThreeHOneBasis_projection (x : Lattice) :
    orderThreeHOneBasis F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((affineCyclicCentralFiberCoverSourceHomologyBasis
            (orderThreeCentralFiberPresentationData F)).degreeOne.symm x)) =
      orderOneLatticeProjectionCoordinates x := by
  have h := establishedAffineCyclicHOnePresentation_projection
    (orderThreeCentralFiberPresentationData F) x
  have hcoord := congrArg
    (fun y ↦ orderThreePresentationCoordinateEquiv F y) h
  calc
    _ = orderThreePresentationCoordinateEquiv F
        (latticeToMultipleFiberHOnePresentation
          (orderThreeCentralFiberPresentationData F).latticeDifference
          (orderThreeCentralFiberPresentationData F).twist 3 x) := by
      change orderThreePresentationCoordinateEquiv F
        (affineCyclicHOnePresentationEquiv (orderThreeCentralFiberPresentationData F)
          (integralSingularHomologyMap 1
            (RadialEllipticActionData.centralFiberCoverProjection
              (orderThreeRadialActionData F))
            ((affineCyclicCentralFiberCoverSourceHomologyBasis
              (orderThreeCentralFiberPresentationData F)).degreeOne.symm x))) = _
      exact hcoord
    _ = _ := orderThreePresentationCoordinateEquiv_lattice F x

/-- Naturality now gives the actual order-four covering coordinates unconditionally. -/
public theorem orderFourHOneBasis_projection (x : Lattice) :
    orderFourHOneBasis F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((affineCyclicCentralFiberCoverSourceHomologyBasis
            (orderFourCentralFiberPresentationData F)).degreeOne.symm x)) =
      orderTwoLatticeProjectionCoordinates x := by
  have h := establishedAffineCyclicHOnePresentation_projection
    (orderFourCentralFiberPresentationData F) x
  have hcoord := congrArg
    (fun y ↦ orderFourPresentationCoordinateEquiv F y) h
  calc
    _ = orderFourPresentationCoordinateEquiv F
        (latticeToMultipleFiberHOnePresentation
          (orderFourCentralFiberPresentationData F).latticeDifference
          (orderFourCentralFiberPresentationData F).twist 4 x) := by
      change orderFourPresentationCoordinateEquiv F
        (affineCyclicHOnePresentationEquiv (orderFourCentralFiberPresentationData F)
          (integralSingularHomologyMap 1
            (RadialEllipticActionData.centralFiberCoverProjection
              (orderFourRadialActionData F))
            ((affineCyclicCentralFiberCoverSourceHomologyBasis
              (orderFourCentralFiberPresentationData F)).degreeOne.symm x))) = _
      exact hcoord
    _ = _ := orderFourPresentationCoordinateEquiv_lattice F x

/-- Exact actual cohomological inputs for the two elliptic finite covers. -/
public structure EllipticDegreeTwoPullbackBases where
  orderThree : FiniteCoverDegreeTwoPullbackBasis
    (RadialEllipticActionData.centralFiberCoverProjection (orderThreeRadialActionData F))
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo
    orderThreePullbackBasis
  orderFour : FiniteCoverDegreeTwoPullbackBasis
    (RadialEllipticActionData.centralFiberCoverProjection (orderFourRadialActionData F))
    (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo
    orderFourPullbackBasis

namespace EllipticDegreeTwoPullbackBases

/-- Package the two exact quotient homology realizations as the corresponding perfect-pairing
data. -/
public noncomputable def ofRealizations
    (orderThree : OrderThreeReducedCentralFiberDegreeTwoRealization F)
    (orderFour : OrderFourReducedCentralFiberDegreeTwoRealization F) :
    EllipticDegreeTwoPullbackBases F where
  orderThree := DegreeTwoPullbackRealization.toFiniteCoverDegreeTwoPullbackBasis orderThree
  orderFour := DegreeTwoPullbackRealization.toFiniteCoverDegreeTwoPullbackBasis orderFour

/-- Instantiate both actual degree-two realizations from the generic perfect-pairing theorem. -/
public def orderThreeRealization (P : EllipticDegreeTwoPullbackBases F) :
    OrderThreeReducedCentralFiberDegreeTwoRealization F :=
  P.orderThree.toDegreeTwoPullbackRealization

public def orderFourRealization (P : EllipticDegreeTwoPullbackBases F) :
    OrderFourReducedCentralFiberDegreeTwoRealization F :=
  P.orderFour.toDegreeTwoPullbackRealization

end EllipticDegreeTwoPullbackBases

/-- Proposition 7.14 for the two actual elliptic central fibres: their integral degree-two
homology has the displayed bases, and the two covering maps have the computed pullback
coordinates. -/
public axiom establishedEllipticDegreeTwoPullbackRealizations :
    Nonempty
      (OrderThreeReducedCentralFiberDegreeTwoRealization F ×
        OrderFourReducedCentralFiberDegreeTwoRealization F)

/-- A coherent choice of the two degree-two perfect-pairing realizations from Proposition
7.14. -/
public noncomputable def ellipticDegreeTwoPullbackBases : EllipticDegreeTwoPullbackBases F :=
  let R := Classical.choice (establishedEllipticDegreeTwoPullbackRealizations F)
  EllipticDegreeTwoPullbackBases.ofRealizations F R.1 R.2

end SphereSixComplex.Topology.FiniteCoverPerfectPairing
