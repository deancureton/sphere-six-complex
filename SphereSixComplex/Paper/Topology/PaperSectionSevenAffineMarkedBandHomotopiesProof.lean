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

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.EllipticFilling

public theorem orderThreeSelectedFilling_toFun_starToFilling_mk
    (A : AnalyticData)
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
    (A : AnalyticData)
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




end SphereSixComplex.Geometry.AnalyticData

end
