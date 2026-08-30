module

public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis
public import SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra

/-!
# First homology data for reduced elliptic fibres

This file contains the definitions shared by the topological reduction and the application to
the order-three and order-four reduced central fibres.
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
  lift_continuous : Continuous affine.lift
  lift_symm_continuous : Continuous affine.lift.symm
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

end EstablishedAffineCyclicQuotientHomology

end

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
