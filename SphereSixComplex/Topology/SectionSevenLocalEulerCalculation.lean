module

public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction
public import SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
public import SphereSixComplex.Topology.SectionSevenMayerVietorisEuler

/-!
# Local Euler calculation for the Section 7 star

The seven local values in the Mayer--Vietoris formula are `0, 2, 0, 0, 0, 0, 0`.
This file performs the exact transport from supplied deformation-retraction data for the three
filling pieces and isolates the four still missing geometric calculations: the cusp
central fibre, the two reduced bielliptic fibres, and the central/collar torus bundles.

No value of the Euler characteristic of the glued space is assumed here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

/-- The six-dimensional integral-homology Euler characteristic is invariant under homotopy
equivalence. -/
public theorem integralHomologyEulerCharacteristicSix_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    integralHomologyEulerCharacteristicSix X =
      integralHomologyEulerCharacteristicSix Y := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(integralSingularHomologyEquivOfHomotopyEquiv 0 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 1 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 2 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 3 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 4 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 5 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 6 e).toIntLinearEquiv.finrank_eq]

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open Topology.PaperEllipticFillingRadialRetraction

variable (A : PaperAnalyticData)

/-- Proposition 7.2 transports the Euler calculation of the cusp central fibre to the actual
cusp filling. -/
public theorem cuspFilling_euler_eq_of_centralFiberRetraction
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness)
    (hCore : integralHomologyEulerCharacteristicSix
      (R.quotientCentralFiber A.starCuspWitness) = 2) :
    integralHomologyEulerCharacteristicSix (A.openEmbeddingStarData.filling 0) = 2 := by
  change integralHomologyEulerCharacteristicSix
      (actualLocalCuspFilling A.starCuspWitness) = 2
  exact (integralHomologyEulerCharacteristicSix_homotopyEquiv
    (R.quotientCentralFiberHomotopyEquiv A.starCuspWitness)).trans hCore

/-- The affine radial chart transports the zero Euler characteristic of the order-three reduced
bielliptic fibre to the actual varying filling. -/
public theorem orderThreeFilling_euler_eq_zero_of_affineRadialChart
    (C : OrderThreeAffineRadialWholeFillingCompatibility A
      A.starSeparation.orderThree.radius)
    (hCore : integralHomologyEulerCharacteristicSix
      (OrderThreeReducedCentralFiber A.periods) = 0) :
    integralHomologyEulerCharacteristicSix (A.openEmbeddingStarData.filling 1) = 0 := by
  change integralHomologyEulerCharacteristicSix
      (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) = 0
  exact (integralHomologyEulerCharacteristicSix_homotopyEquiv
    (orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
      A.starSeparation.orderThree.radius C)).trans hCore

/-- The affine radial chart transports the zero Euler characteristic of the order-four reduced
bielliptic fibre to the actual varying filling. -/
public theorem orderFourFilling_euler_eq_zero_of_affineRadialChart
    (C : OrderFourAffineRadialWholeFillingCompatibility A
      A.starSeparation.orderFour.radius)
    (hCore : integralHomologyEulerCharacteristicSix
      (OrderFourReducedCentralFiber A.periods) = 0) :
    integralHomologyEulerCharacteristicSix (A.openEmbeddingStarData.filling 2) = 0 := by
  change integralHomologyEulerCharacteristicSix
      (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) = 0
  exact (integralHomologyEulerCharacteristicSix_homotopyEquiv
    (orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
      A.starSeparation.orderFour.radius C)).trans hCore

/-- The exact local calculation after transporting the three filling values through the source
deformation retractions.  The remaining hypotheses are precisely the finite-torus-bundle Euler
calculations for the central piece and collars and the finite-cell/finite-quotient calculations for
the three reduced central fibres. -/
public theorem sectionSevenLocalEulerExpression_eq_two_of_modelCalculations
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness)
    (C₃ : OrderThreeAffineRadialWholeFillingCompatibility A
      A.starSeparation.orderThree.radius)
    (C₄ : OrderFourAffineRadialWholeFillingCompatibility A
      A.starSeparation.orderFour.radius)
    (hCentral : integralHomologyEulerCharacteristicSix
      A.openEmbeddingStarData.central = 0)
    (hCuspCore : integralHomologyEulerCharacteristicSix
      (R.quotientCentralFiber A.starCuspWitness) = 2)
    (hThreeCore : integralHomologyEulerCharacteristicSix
      (OrderThreeReducedCentralFiber A.periods) = 0)
    (hFourCore : integralHomologyEulerCharacteristicSix
      (OrderFourReducedCentralFiber A.periods) = 0)
    (hCollar : ∀ i : Fin 3, integralHomologyEulerCharacteristicSix
      (A.openEmbeddingStarData.collarSource i) = 0) :
    A.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2 := by
  have hFillZero := A.cuspFilling_euler_eq_of_centralFiberRetraction R hCuspCore
  have hFillOne := A.orderThreeFilling_euler_eq_zero_of_affineRadialChart C₃ hThreeCore
  have hFillTwo := A.orderFourFilling_euler_eq_zero_of_affineRadialChart C₄ hFourCore
  unfold OpenEmbeddingStarData.sectionSevenLocalEulerExpression
  rw [hCentral, hFillZero, hFillOne, hFillTwo, hCollar 0, hCollar 1, hCollar 2]
  norm_num

end Geometry.PaperAnalyticData

end SphereSixComplex
