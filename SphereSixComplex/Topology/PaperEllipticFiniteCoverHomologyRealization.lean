module

public import SphereSixComplex.Topology.FiniteCoverPerfectPairing

/-!
# Homology realization for the two elliptic finite covers

The affine-cyclic presentation supplies degree-one naturality in the fixed production bases. The
degree-two coordinates are supplied by the exact integral calculation in Proposition 7.14.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Topology.FiniteCoverPerfectPairing

open Geometry Geometry.AnalyticTorusFamily Geometry.EllipticFamilySpecialization
open Geometry.GlobalTorusFamily
open LatticeData PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels PaperLemmaSevenThirteenAlgebra
open PaperMultipleFiberHOneTopology
open PaperAffineCyclicQuotientHomologyCoordinates

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

/-- The fixed production basis has the required order-three covering coordinates. -/
public theorem orderThreeFixedHOneBasis_projection (x : Lattice) :
    (orderThreeReducedCentralFiberHOneEquivIntSquared F).toAddEquiv
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      orderOneLatticeProjectionCoordinates x := by
  change orderThreeReducedCentralFiberHOneEquivIntSquared F
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData F))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) = _
  rw [orderThreeReducedCentralFiberHOneEquivIntSquared_projection_raw,
    orderOneSelectedPresentationEquivIntSquared_mk]
  funext i
  fin_cases i <;>
    simp [orderOnePresentationCoordinates, orderOneLatticeProjectionCoordinates,
      orderOneCoinvariantsEquivIntSquared_mk, orderOneCoordinates, psiOne]

/-- The fixed production basis has the required order-four covering coordinates. -/
public theorem orderFourFixedHOneBasis_projection (x : Lattice) :
    (orderFourReducedCentralFiberHOneEquivIntSquared F).toAddEquiv
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) =
      orderTwoLatticeProjectionCoordinates x := by
  change orderFourReducedCentralFiberHOneEquivIntSquared F
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData F))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) = _
  rw [orderFourReducedCentralFiberHOneEquivIntSquared_projection_raw,
    orderTwoSelectedPresentationEquivIntSquared_mk]
  funext i
  fin_cases i <;>
    simp [orderTwoPresentationCoordinates, orderTwoLatticeProjectionCoordinates,
      orderTwoCoinvariantsEquivIntSquared_mk, orderTwoCoordinates, psiTwo]

/-- Degree-one naturality for the actual order-three finite cover. -/
public theorem orderThreeHOneNaturality : OrderThreeCentralFiberHOneNaturality F where
  projection_coordinates := orderThreeFixedHOneBasis_projection F

/-- Degree-one naturality for the actual order-four finite cover. -/
public theorem orderFourHOneNaturality : OrderFourCentralFiberHOneNaturality F where
  projection_coordinates := orderFourFixedHOneBasis_projection F

namespace EllipticDegreeTwoPullbackBases

/-- Construct the finite-cover homology realization from the two degree-two perfect-pairing
inputs. -/
public def toEllipticFiniteCoverHomologyRealization
    (P : EllipticDegreeTwoPullbackBases F) :
    EllipticFiniteCoverHomologyRealization F where
  orderThreeOne := orderThreeHOneNaturality F
  orderFourOne := orderFourHOneNaturality F
  orderThreeTwo := P.orderThreeRealization
  orderFourTwo := P.orderFourRealization

end EllipticDegreeTwoPullbackBases

/-- The actual degree-one and degree-two homology realization for both elliptic finite
covers. -/
public noncomputable def ellipticFiniteCoverHomologyRealization :
    EllipticFiniteCoverHomologyRealization F :=
  EllipticDegreeTwoPullbackBases.toEllipticFiniteCoverHomologyRealization F
    (ellipticDegreeTwoPullbackBases F)

end SphereSixComplex.Topology.FiniteCoverPerfectPairing

end

end
