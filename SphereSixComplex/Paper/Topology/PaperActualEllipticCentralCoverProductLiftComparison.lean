module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticWholeRelatorClassificationProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction
public import SphereSixComplex.Paper.Topology.PaperEllipticCollarLoopClassProof

/-!
# Product-lift comparison for the complete elliptic relations

The Cayley-coordinate calculation and the principal-gauge calculation determine the complete
central affine deck products.  This file reduces each whole-relator chart identity to one
endpoint calculation for the lift of the complete regular loop to the based-path universal
cover.  Thus the remaining input is a single point-set comparison for each elliptic point, not
independent choices for the meridian and fibre generators.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup

variable (A : AnalyticData)













/-- In the local product coordinates, the complete order-three regular loop is exactly the
one-turn Cayley loop together with the principal-gauge loop and its fixed fibre offset. -/
public theorem orderThreeFillingRelationRegularLoop_localProductCoordinate
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    (((orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods
            (A.orderThreeCollarInverseRepresentative
              (A.ellipticThreeBoundaryDeckStraightLift
                A.ellipticThreeBoundaryDeckData.fillingRelation t)).1) :
            ComplexUnitDisc) : ℂ),
      (orderThreeRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderThreeFillingRelationRegularLoop t))).2) =
      ((A.orderThreeFillingRelationCayleyLoop t).1,
        A.orderThreeFillingRelationPrincipalGaugeLoop t +
          Quotient.mk _ A.ellipticThreeBoundaryBase.2.2) := by
  let _ := A.ellipticThreeBoundaryAction
  apply Prod.ext
  · exact A.orderThreeFillingRelationCayleyLoop_apply t
  · rw [A.orderThreeFillingRelationRegularLoop_realPeriod_snd]
    rw [A.orderThreeFillingRelationPrincipalGaugeLoop_apply]

/-- The analogous exact local-product description of the order-four complete loop. -/
public theorem orderFourFillingRelationRegularLoop_localProductCoordinate
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    (((orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods
            (A.orderFourCollarInverseRepresentative
              (A.ellipticFourBoundaryDeckStraightLift
                A.ellipticFourBoundaryDeckData.fillingRelation t)).1) :
            ComplexUnitDisc) : ℂ),
      (orderFourRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderFourFillingRelationRegularLoop t))).2) =
      ((A.orderFourFillingRelationCayleyLoop t).1,
        A.orderFourFillingRelationPrincipalGaugeLoop t +
          Quotient.mk _ A.ellipticFourBoundaryBase.2.2) := by
  let _ := A.ellipticFourBoundaryAction
  apply Prod.ext
  · exact A.orderFourFillingRelationCayleyLoop_apply t
  · rw [A.orderFourFillingRelationRegularLoop_realPeriod_snd]
    rw [A.orderFourFillingRelationPrincipalGaugeLoop_apply]

















end SphereSixComplex.Geometry.AnalyticData

end

end
