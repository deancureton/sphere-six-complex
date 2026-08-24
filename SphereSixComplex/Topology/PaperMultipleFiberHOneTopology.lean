module

public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis
public import SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra

/-!
# First homology of the reduced elliptic fibres

This file isolates the standard covering-space calculation for a free affine cyclic quotient
of a torus.  The hypotheses retain the affine lift, including the lattice translation made by
its full cyclic iterate, so the resulting multiple-fibre presentation records the correct
extension class rather than only the linear monodromy.
-/

open AlgebraicTopology

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus Geometry.GlobalTorusFamily
open Geometry.EllipticFamilySpecialization Geometry.EllipticFixedPointCriterion
open LatticeData Periods TriangleGroup
open PaperEllipticFillingRadialRetraction
open PaperLemmaSevenThirteenAlgebra TwistObstruction

noncomputable section

/-- Exact input for the standard fundamental-group presentation of a free affine cyclic torus
quotient.  The last equation says that the chosen lift of the cyclic generator has full iterate
equal to translation by the lattice vector `twist`. -/
public structure AffineCyclicCentralFiberPresentationData
    (m : ℕ) [NeZero m] (p : SphereSixComplex.Periods.Parameters)
    (D : RadialEllipticActionData m (AdditiveTorus p)) where
  fullRank : FullRank p
  affine : DescendedAffineTorusAutomorphism p
  latticeDifference : Lattice →ₗ[ℤ] Lattice
  latticeDifference_eq :
    latticeDifference = affine.latticeMap.toLinearMap - LinearMap.id
  twist : Lattice
  translationVector_eq : D.actionData.translationVector = twist
  liftTranslation : ComplexTwoSpace
  translation_mk :
    affine.translation = (Quotient.mk _ liftTranslation : AdditiveTorus p)
  generator_eq : ∀ x, D.actionData.fiberGenerator x = affine.map x
  lift_full_iterate : ∀ z,
    (affineEquiv affine.lift liftTranslation ^ m) z = z + periodVector p twist
  free : letI := D.actionData.diagonalAction
    IsCancelSMul (FiniteCyclic m) D.Product

namespace EstablishedAffineCyclicQuotientHomology

/-- For a free affine action of a finite cyclic group on a full-rank torus, first integral
homology is the abelianization of the standard covering-group presentation.  Thus it is the
coinvariants of the lattice together with a meridian, subject to the relation that `m` times
the meridian is the full-iterate lattice translation.

This combines the standard identification of first homology with the abelianized fundamental
group and the usual presentation of the fundamental group of a free affine cyclic torus
quotient. -/
public axiom reducedCentralFiberHOneEquivPresentation
    {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
    {D : RadialEllipticActionData m (AdditiveTorus p)}
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    IntegralSingularHomology 1 D.reducedCentralFiber ≃ₗ[ℤ]
      MultipleFiberHOnePresentation
        P.latticeDifference P.twist (m : ℤ)

end EstablishedAffineCyclicQuotientHomology

variable {U : TriangleUniformization} (F : PeriodFunctions U)

private theorem orderThreeLiftTranslation_fixed :
    (orderThreeDescendedAffineTorusAutomorphism F).lift
        ((3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) =
      (3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon := by
  change periodTransport g₁ (parameterMap F U.zOne)
      ((3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) = _
  rw [map_smul]
  rw [periodTransport_periodVector, rhoLambda_g₁_apply, A₁_epsilon]
  rw [parameterMap_zOne_fixed F]

private theorem orderFourLiftTranslation_fixed :
    (orderFourDescendedAffineTorusAutomorphism F).lift
        ((4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) =
      (4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon') := by
  change periodTransport g₂ (parameterMap F U.zTwo)
      ((4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) = _
  rw [map_smul]
  rw [periodTransport_periodVector, rhoLambda_g₂_apply, Matrix.mulVec_neg, A₂_epsilon']
  rw [parameterMap_zTwo_fixed F]

/-- The actual order-three reduced fibre supplies all inputs to the general affine cyclic
quotient calculation. -/
@[expose] public def orderThreeCentralFiberPresentationData :
    AffineCyclicCentralFiberPresentationData 3 (parameterMap F U.zOne).1
      (orderThreeRadialActionData F) where
  fullRank := fullRankDomain (parameterMap F U.zOne)
  affine := orderThreeDescendedAffineTorusAutomorphism F
  latticeDifference := orderOneDifference
  latticeDifference_eq := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sub_apply, LinearMap.id_apply, orderOneDifference_apply]
    exact (congrArg (fun y ↦ y - x) (rhoLambda_g₁_apply x)).symm
  twist := epsilon
  translationVector_eq := rfl
  liftTranslation := (3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon
  translation_mk := by
    change Quotient.mk _ ((3 : ℂ)⁻¹ • periodVector _ epsilon) =
      Quotient.mk _ ((3 : ℝ)⁻¹ • periodVector _ epsilon)
    congr 1
    ext i
    norm_num
  generator_eq _ := rfl
  lift_full_iterate z := by
    rw [affineEquiv_pow_apply _ _ (orderThreeLiftTranslation_fixed F)]
    change periodTransport g₁ (parameterMap F U.zOne)
        (periodTransport g₁ (parameterMap F U.zOne)
          (periodTransport g₁ (parameterMap F U.zOne) z)) +
        3 • ((3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) = _
    rw [periodTransport_gOne_three]
    congr 1
    ext i
    simp
  free := orderThreeAction_free F

/-- The actual order-four reduced fibre supplies all inputs to the general affine cyclic
quotient calculation. -/
@[expose] public def orderFourCentralFiberPresentationData :
    AffineCyclicCentralFiberPresentationData 4 (parameterMap F U.zTwo).1
      (orderFourRadialActionData F) where
  fullRank := fullRankDomain (parameterMap F U.zTwo)
  affine := orderFourDescendedAffineTorusAutomorphism F
  latticeDifference := orderTwoDifference
  latticeDifference_eq := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sub_apply, LinearMap.id_apply, orderTwoDifference_apply]
    exact (congrArg (fun y ↦ y - x) (rhoLambda_g₂_apply x)).symm
  twist := -epsilon'
  translationVector_eq := rfl
  liftTranslation := (4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')
  translation_mk := by
    change Quotient.mk _ ((4 : ℂ)⁻¹ • periodVector _ (-epsilon')) =
      Quotient.mk _ ((4 : ℝ)⁻¹ • periodVector _ (-epsilon'))
    congr 1
    ext i
    norm_num
  generator_eq _ := rfl
  lift_full_iterate z := by
    rw [affineEquiv_pow_apply _ _ (orderFourLiftTranslation_fixed F)]
    change periodTransport g₂ (parameterMap F U.zTwo)
        (periodTransport g₂ (parameterMap F U.zTwo)
          (periodTransport g₂ (parameterMap F U.zTwo)
            (periodTransport g₂ (parameterMap F U.zTwo) z))) +
        4 • ((4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) = _
    rw [periodTransport_gTwo_four]
    congr 1
    ext i
    simp
  free := orderFourAction_free F

/-- First integral homology of the actual order-three reduced elliptic fibre, with the exact
multiple-fibre presentation from Lemma 7.13. -/
public noncomputable def orderThreeReducedCentralFiberHOneEquivPresentation :
    IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) ≃ₗ[ℤ]
      OrderOneSelectedPresentation := by
  exact EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation
    (orderThreeCentralFiberPresentationData F)

/-- First integral homology of the actual order-four reduced elliptic fibre, with the exact
multiple-fibre presentation from Lemma 7.13. -/
public noncomputable def orderFourReducedCentralFiberHOneEquivPresentation :
    IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) ≃ₗ[ℤ]
      OrderTwoSelectedPresentation := by
  exact EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation
    (orderFourCentralFiberPresentationData F)

/-- In particular, first integral homology of the actual order-three reduced fibre is free of
rank two. -/
public noncomputable def orderThreeReducedCentralFiberHOneEquivIntSquared :
    IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) ≃ₗ[ℤ] IntSquared :=
  (orderThreeReducedCentralFiberHOneEquivPresentation F).trans
    orderOneSelectedPresentationEquivIntSquared

/-- In particular, first integral homology of the actual order-four reduced fibre is free of
rank two. -/
public noncomputable def orderFourReducedCentralFiberHOneEquivIntSquared :
    IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) ≃ₗ[ℤ] IntSquared :=
  (orderFourReducedCentralFiberHOneEquivPresentation F).trans
    orderTwoSelectedPresentationEquivIntSquared

end

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
