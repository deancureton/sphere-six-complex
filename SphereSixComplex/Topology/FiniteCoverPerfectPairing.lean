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
open PaperPropositionSevenFourteenDegreeTwoAlgebra TriangleGroup TwistObstruction

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

private noncomputable def orderThreeReducedCentralFiberFiniteCWModel
    {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U) :
    FiniteCWModelSix (OrderThreeReducedCentralFiber F) := by
  let p := parameterMap F U.zOne
  let P := orderThreeCentralFiberPresentationData F
  apply AffineFiniteCyclicTorusCW.finiteCWModelSix_reducedCentralFiber_of_affineGenerator
    p.1 P.fullRank (orderThreeRadialActionData F)
    (periodTransport g₁ p) ((3 : ℂ)⁻¹ • periodVector p.1 epsilon)
  · intro z
    change affineEquiv (orderThreeFiberAutomorphism F)
        (orderThreeTranslation p.1) (Quotient.mk _ z) = _
    rw [affineEquiv_apply, orderThreeFiberAutomorphism_mk]
    change Quotient.mk _ (periodTransport g₁ p z) +
        additiveTorusProjection p.1 ((3 : ℂ)⁻¹ • periodVector p.1 epsilon) = _
    exact (additiveTorusProjection_add p.1 _ _).symm
  · exact P.free

private noncomputable def orderFourReducedCentralFiberFiniteCWModel
    {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U) :
    FiniteCWModelSix (OrderFourReducedCentralFiber F) := by
  let p := parameterMap F U.zTwo
  let P := orderFourCentralFiberPresentationData F
  apply AffineFiniteCyclicTorusCW.finiteCWModelSix_reducedCentralFiber_of_affineGenerator
    p.1 P.fullRank (orderFourRadialActionData F)
    (periodTransport g₂ p) ((4 : ℂ)⁻¹ • periodVector p.1 (-epsilon'))
  · intro z
    change affineEquiv (orderFourFiberAutomorphism F)
        (orderFourTranslation p.1) (Quotient.mk _ z) = _
    rw [affineEquiv_apply, orderFourFiberAutomorphism_mk]
    change Quotient.mk _ (periodTransport g₂ p z) +
        additiveTorusProjection p.1 ((4 : ℂ)⁻¹ • periodVector p.1 (-epsilon')) = _
    exact (additiveTorusProjection_add p.1 _ _).symm
  · exact P.free

private theorem dualEval_bijective_of_finite_torsionFree
    {X : Type} [TopologicalSpace X]
    (hFinite : Module.Finite ℤ (IntegralSingularHomology 2 X))
    (hTorsionFree : Module.IsTorsionFree ℤ (IntegralSingularHomology 2 X)) :
    Function.Bijective (Module.Dual.eval ℤ (IntegralSingularHomology 2 X)) := by
  let _ : Module.Finite ℤ (IntegralSingularHomology 2 X) := hFinite
  let _ : Module.IsTorsionFree ℤ (IntegralSingularHomology 2 X) := hTorsionFree
  let hFree : Module.Free ℤ (IntegralSingularHomology 2 X) :=
    Module.free_of_finite_type_torsion_free'
  let _ := hFree
  let b := Module.Free.chooseBasis ℤ (IntegralSingularHomology 2 X)
  exact ⟨b.eval_injective, LinearMap.range_eq_top.mp b.eval_range⟩

/-- The remaining transfer input after finite generation has been obtained from the explicit
affine finite-CW models.  It records only the two pulled-back dual bases and the torsion-freeness
needed to turn finite generation into integral reflexivity. -/
public structure EllipticDegreeTwoDualPullbackData where
  orderThreeDualBasis : Module.Basis (Fin 2) ℤ
    (Module.Dual ℤ (IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F)))
  orderThreeTorsionFree :
    Module.IsTorsionFree ℤ
      (IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F))
  orderThreePullback_apply : ∀ (i : Fin 2) (x : DegreeTwoLattice),
    orderThreeDualBasis i
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      degreeTwoEvaluation (orderThreePullbackBasis i) x
  orderFourDualBasis : Module.Basis (Fin 2) ℤ
    (Module.Dual ℤ (IntegralSingularHomology 2 (OrderFourReducedCentralFiber F)))
  orderFourTorsionFree :
    Module.IsTorsionFree ℤ
      (IntegralSingularHomology 2 (OrderFourReducedCentralFiber F))
  orderFourPullback_apply : ∀ (i : Fin 2) (x : DegreeTwoLattice),
    orderFourDualBasis i
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      degreeTwoEvaluation (orderFourPullbackBasis i) x

/-- The exact residual transfer statement: the two computed pullback families are dual bases,
and the quotient degree-two homology groups contain no torsion. -/
public axiom establishedEllipticDegreeTwoDualPullbackData :
    Nonempty (EllipticDegreeTwoDualPullbackData F)

/-- The exact remaining cohomological input from Proposition 7.14: the displayed pullback
classes are bases of the integral dual lattices of the two elliptic central fibres, and their
integral evaluation pairings are perfect. -/
public theorem establishedEllipticDegreeTwoPullbackBases :
    Nonempty (EllipticDegreeTwoPullbackBases F) := by
  obtain ⟨D⟩ := establishedEllipticDegreeTwoDualPullbackData F
  refine ⟨{ orderThree := ?_, orderFour := ?_ }⟩
  · exact
      { quotientDualBasis := D.orderThreeDualBasis
        reflexive := dualEval_bijective_of_finite_torsionFree
          ((orderThreeReducedCentralFiberFiniteCWModel F).integralHomologyFiniteSix.finiteHomology
            2)
          D.orderThreeTorsionFree
        pullback_apply := D.orderThreePullback_apply }
  · exact
      { quotientDualBasis := D.orderFourDualBasis
        reflexive := dualEval_bijective_of_finite_torsionFree
          ((orderFourReducedCentralFiberFiniteCWModel F).integralHomologyFiniteSix.finiteHomology 2)
          D.orderFourTorsionFree
        pullback_apply := D.orderFourPullback_apply }

/-- Proposition 7.14 for the two actual elliptic central fibres: their integral degree-two
homology has the displayed bases, and the two covering maps have the computed pullback
coordinates. -/
public theorem establishedEllipticDegreeTwoPullbackRealizations :
    Nonempty
      (OrderThreeReducedCentralFiberDegreeTwoRealization F ×
        OrderFourReducedCentralFiberDegreeTwoRealization F) := by
  obtain ⟨P⟩ := establishedEllipticDegreeTwoPullbackBases F
  exact ⟨P.orderThreeRealization F, P.orderFourRealization F⟩

/-- A coherent choice of the two degree-two perfect-pairing realizations from Proposition
7.14. -/
public noncomputable def ellipticDegreeTwoPullbackBases : EllipticDegreeTwoPullbackBases F :=
  Classical.choice (establishedEllipticDegreeTwoPullbackBases F)

end SphereSixComplex.Topology.FiniteCoverPerfectPairing
