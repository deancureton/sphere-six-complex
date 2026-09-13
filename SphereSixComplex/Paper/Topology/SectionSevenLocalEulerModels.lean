module

public import SphereSixComplex.Prerequisites.Topology.FiniteCWModelSix

public import SphereSixComplex.Paper.Topology.EllipticReducedFiberMappingTorusHomology
public import SphereSixComplex.Prerequisites.Topology.FiniteBouquetMappingTorusEuler
public import SphereSixComplex.Paper.Topology.SectionSevenLocalEulerCalculation
public import SphereSixComplex.Paper.Topology.StandardFourTorusHomologicalModel

/-!
# Homology and Euler characteristics of the local pieces

Retractions and mapping-torus models supply finite integral homology for the seven local spaces.
The cusp contributes Euler characteristic two; the other local pieces contribute zero.
These inputs give the Euler characteristic of the glued space.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.AnalyticData

open CuspCollar
open EllipticFilling

variable (A : AnalyticData)

/-- The exact homological information required from the regular central family. -/
public structure CentralHomologyEulerModel
    (X : Type) [TopologicalSpace X] : Prop where
  integralHomologyFiniteSix : IntegralHomologyFiniteSix X
  euler_eq_zero : integralHomologyEulerCharacteristicSix X = 0

/-- Retractions, finite homology, Euler characteristics, and collar mapping-torus models
for the seven local spaces. -/
public structure LocalEulerModels where
  cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness
  orderThreeRadialChart : OrderThreeAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderThree.radius
  orderFourRadialChart : OrderFourAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderFour.radius
  centralModel : CentralHomologyEulerModel A.openEmbeddingStarData.central
  cuspHomologyFinite : IntegralHomologyFiniteSix
    (cuspRetraction.quotientCentralFiber A.starCuspWitness)
  cuspEuler_eq_two : integralHomologyEulerCharacteristicSix
    (cuspRetraction.quotientCentralFiber A.starCuspWitness) = 2
  collarModel : ∀ i : Fin 3, FourTorusCircleMappingTorusModel
    (A.openEmbeddingStarData.collarSource i)

namespace LocalEulerModels

/-- All seven local spaces have finite integral homology supported in degrees at most six. -/
public theorem localIntegralHomologyFiniteSix (M : LocalEulerModels A) :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.filling i)) ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource i)) := by
  refine ⟨M.centralModel.integralHomologyFiniteSix, ?_, fun i ↦
    (M.collarModel i).integralHomologyFiniteSix⟩
  intro i
  fin_cases i
  · change IntegralHomologyFiniteSix (ActualLocalCuspFilling A.starCuspWitness)
    exact M.cuspHomologyFinite.homotopyEquiv
      (M.cuspRetraction.quotientCentralFiberHomotopyEquiv A.starCuspWitness).symm
  · change IntegralHomologyFiniteSix
      (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
    exact Topology.EllipticReducedFiberMappingTorusHomology.orderThreeIntegralHomologyFiniteSix
      A.periods |>.homotopyEquiv
      (orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
        A.starSeparation.orderThree.radius M.orderThreeRadialChart).symm
  · change IntegralHomologyFiniteSix
      (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)
    exact Topology.EllipticReducedFiberMappingTorusHomology.orderFourIntegralHomologyFiniteSix
      A.periods |>.homotopyEquiv
      (orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
        A.starSeparation.orderFour.radius M.orderFourRadialChart).symm

/-- The exact Section 7 local Euler calculation, derived from geometric models. -/
public theorem sectionSevenLocalEulerExpression_eq_two (M : LocalEulerModels A) :
    A.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2 :=
  A.localEulerExpression_eq_two_of_modelCalculations
    M.cuspRetraction M.orderThreeRadialChart M.orderFourRadialChart
    M.centralModel.euler_eq_zero M.cuspEuler_eq_two
    (Topology.EllipticReducedFiberMappingTorusHomology.orderThreeEuler_eq_zero A.periods)
    (Topology.EllipticReducedFiberMappingTorusHomology.orderFourEuler_eq_zero A.periods)
    (fun i ↦ (M.collarModel i).euler_eq_zero)

end LocalEulerModels

end Geometry.AnalyticData

end SphereSixComplex
