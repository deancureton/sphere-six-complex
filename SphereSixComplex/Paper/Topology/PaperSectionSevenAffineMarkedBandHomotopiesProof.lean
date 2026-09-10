module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRealPeriodTransport

/-!
# The marked affine band homotopies

The named affine-strip lift fixes the fibre coordinate of the central-band trivialization.
The explicit affine radial transports preserve that coordinate, so the two marked endpoints are
the canonical finite-cover projections.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

public theorem orderThreeSelectedFilling_toFun_starToFilling_mk
    (A : PaperAnalyticData)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius).carrier) :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.starToFilling 1 (Quotient.mk _ q)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm
            (orderThreeRealPeriodProductHomeomorph A.periods q.1).2) := by
  rfl

public theorem orderFourSelectedFilling_toFun_starToFilling_mk
    (A : PaperAnalyticData)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius).carrier) :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.starToFilling 2 (Quotient.mk _ q)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm
            (orderFourRealPeriodProductHomeomorph A.periods q.1).2) := by
  rfl

/-- The irreducible point-set calculation left by the explicit affine radial deformation.
For every representative of either selected star-collar endpoint, its fixed real-period torus
coordinate has the marked finite-cover class.  All ambient gluing maps, homotopy inverses, and
deformation retractions have been eliminated from this statement. -/
public structure AffineMarkedStarRealPeriodCompatibility
    (A : PaperAnalyticData) : Prop where
  orderThree : ∀ (x : A.affineMarkedBand)
      (q : (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius).carrier),
    A.orderThreeOverlapCollarHomeomorph
        (A.affineOrderThreeDiscOverlapEndpoint x) = Quotient.mk _ q →
      RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)
          ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderThreeRadialActionData A.periods)).symm
              (orderThreeRealPeriodProductHomeomorph A.periods q.1).2) =
        affineBandOrderThreeMarkedProjection A x
  orderFour : ∀ (x : A.affineMarkedBand)
      (q : (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier),
    A.orderFourOverlapCollarHomeomorph
        (A.affineOrderFourDiscOverlapEndpoint x) = Quotient.mk _ q →
      RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)
          ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderFourRadialActionData A.periods)).symm
              (orderFourRealPeriodProductHomeomorph A.periods q.1).2) =
        affineBandOrderFourMarkedProjection A x

/-- The representative-level real-period calculation gives the two exact selected-filling
endpoint equalities. -/
public theorem AffineMarkedStarRealPeriodCompatibility.toStarEndpointCompatibility
    {A : PaperAnalyticData} (H : A.AffineMarkedStarRealPeriodCompatibility) :
    A.AffineMarkedStarEndpointCompatibility := by
  refine { orderThree := ?_, orderFour := ?_ }
  · apply ContinuousMap.ext
    intro x
    let u := A.affineOrderThreeDiscOverlapEndpoint x
    change (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u)) = _
    generalize hq : A.orderThreeOverlapCollarHomeomorph u = q
    induction q using Quotient.inductionOn with
    | _ q =>
      rw [orderThreeSelectedFilling_toFun_starToFilling_mk]
      exact H.orderThree x q hq
  · apply ContinuousMap.ext
    intro x
    let u := A.affineOrderFourDiscOverlapEndpoint x
    change (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u)) = _
    generalize hq : A.orderFourOverlapCollarHomeomorph u = q
    induction q using Quotient.inductionOn with
    | _ q =>
      rw [orderFourSelectedFilling_toFun_starToFilling_mk]
      exact H.orderFour x q hq

public theorem markedBandHomotopies_of_starRealPeriodCompatibility
    (A : PaperAnalyticData) (H : A.AffineMarkedStarRealPeriodCompatibility) :
    A.AffineOverlapBandCompatibility :=
  markedBandHomotopies_of_starEndpointCompatibility A
    H.toStarEndpointCompatibility

end SphereSixComplex.Geometry.PaperAnalyticData

end
