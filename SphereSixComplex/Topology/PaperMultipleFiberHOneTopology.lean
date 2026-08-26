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
open PaperEllipticReducedCentralFiberCoverModels
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

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The standard degree-one homology basis on the source torus of the affine cyclic cover. -/
@[expose] public noncomputable def centralFiberCoverSourceDegreeOneBasis
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    IntegralSingularHomology 1
        (RadialEllipticActionData.centralFiberCoverSource D) ≃+ Lattice :=
  ((EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).homeomorph
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)).degreeOne

/-- The canonical map from the covering lattice to the abelian multiple-fibre presentation. -/
@[expose] public def latticeProjection
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    Lattice →ₗ[ℤ]
      MultipleFiberHOnePresentation P.latticeDifference P.twist (m : ℤ) :=
  (LinearMap.range
      (multipleFiberRelationMap P.latticeDifference P.twist (m : ℤ))).mkQ.comp
    ((LinearMap.range P.latticeDifference).mkQ.prod
      (0 : Lattice →ₗ[ℤ] ℤ))

/-- The standard affine-cyclic quotient calculation together with its naturality under the
covering projection. -/
public structure ReducedCentralFiberHOnePresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) where
  equiv : IntegralSingularHomology 1 D.reducedCentralFiber ≃ₗ[ℤ]
    MultipleFiberHOnePresentation P.latticeDifference P.twist (m : ℤ)
  projection : ∀ x : Lattice,
    equiv
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection D)
          ((centralFiberCoverSourceDegreeOneBasis P).symm x)) =
      latticeProjection P x

/-- The usual presentation theorem for a free affine cyclic torus quotient, including the
canonical value of the presentation coordinates on the covering torus. -/
public axiom reducedCentralFiberHOnePresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    ReducedCentralFiberHOnePresentation P

/-- For a free affine action of a finite cyclic group on a full-rank torus, first integral
homology is the abelianization of the standard covering-group presentation.  Thus it is the
coinvariants of the lattice together with a meridian, subject to the relation that `m` times
the meridian is the full-iterate lattice translation.

This combines the standard identification of first homology with the abelianized fundamental
group and the usual presentation of the fundamental group of a free affine cyclic torus
quotient. -/
public noncomputable def reducedCentralFiberHOneEquivPresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    IntegralSingularHomology 1 D.reducedCentralFiber ≃ₗ[ℤ]
      MultipleFiberHOnePresentation
        P.latticeDifference P.twist (m : ℤ) :=
  (reducedCentralFiberHOnePresentation P).equiv

/-- The presentation equivalence sends the homology map of the covering torus to the canonical
lattice-to-presentation map. -/
public theorem reducedCentralFiberHOneEquivPresentation_projection
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    reducedCentralFiberHOneEquivPresentation P
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection D)
          ((centralFiberCoverSourceDegreeOneBasis P).symm x)) =
      latticeProjection P x :=
  (reducedCentralFiberHOnePresentation P).projection x

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

/-- The fixed order-three coordinates of the covering projection, before evaluating the explicit
presentation-coordinate map. -/
public theorem orderThreeReducedCentralFiberHOneEquivIntSquared_projection_raw (x : Lattice) :
    orderThreeReducedCentralFiberHOneEquivIntSquared F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      orderOneSelectedPresentationEquivIntSquared
        (Submodule.Quotient.mk (Submodule.Quotient.mk x, 0)) := by
  have h :=
    EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation_projection
      (orderThreeCentralFiberPresentationData F) x
  change orderThreeReducedCentralFiberHOneEquivPresentation F
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData F))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      EstablishedAffineCyclicQuotientHomology.latticeProjection
        (orderThreeCentralFiberPresentationData F) x at h
  have hc := congrArg orderOneSelectedPresentationEquivIntSquared h
  change orderOneSelectedPresentationEquivIntSquared
      (orderThreeReducedCentralFiberHOneEquivPresentation F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x))) = _
  exact hc

/-- The fixed order-four coordinates of the covering projection, before evaluating the explicit
presentation-coordinate map. -/
public theorem orderFourReducedCentralFiberHOneEquivIntSquared_projection_raw (x : Lattice) :
    orderFourReducedCentralFiberHOneEquivIntSquared F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      orderTwoSelectedPresentationEquivIntSquared
        (Submodule.Quotient.mk (Submodule.Quotient.mk x, 0)) := by
  have h :=
    EstablishedAffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation_projection
      (orderFourCentralFiberPresentationData F) x
  change orderFourReducedCentralFiberHOneEquivPresentation F
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData F))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      EstablishedAffineCyclicQuotientHomology.latticeProjection
        (orderFourCentralFiberPresentationData F) x at h
  have hc := congrArg orderTwoSelectedPresentationEquivIntSquared h
  change orderTwoSelectedPresentationEquivIntSquared
      (orderFourReducedCentralFiberHOneEquivPresentation F
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x))) = _
  exact hc

end

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
