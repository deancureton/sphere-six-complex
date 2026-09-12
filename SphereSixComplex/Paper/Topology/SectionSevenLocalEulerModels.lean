module

public import SphereSixComplex.Prerequisites.Topology.FiniteCWModelSix

public import SphereSixComplex.Paper.Topology.EllipticReducedFiberMappingTorusHomology
public import SphereSixComplex.Prerequisites.Topology.FiniteBouquetMappingTorusEuler
public import SphereSixComplex.Paper.Topology.SectionSevenLocalEulerCalculation
public import SphereSixComplex.Paper.Topology.StandardFourTorusHomologicalModel

/-!
# Finite CW models for the Section 7 local Euler calculation

This file proves the required finite-CW Euler--Poincaré results and states the finite-cover Euler
formula at its natural level.  It then reduces the seven local values to geometric CW and covering
models.  The resulting Section 7 contract contains no homology ranks and no Euler values.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- The source CW decomposition of the cusp fibre: the three rational curves in the double locus
share two vertices and contribute three edges and three faces; the complement contributes one
relative 2-cell, two relative 3-cells, and one relative 4-cell. -/
public structure CuspToricCellModel (X : Type) [TopologicalSpace X] where
  toFiniteCWModelSix : FiniteCWModelSix X
  cellsZero : toFiniteCWModelSix.cellCount 0 = 2
  cellsOne : toFiniteCWModelSix.cellCount 1 = 3
  cellsTwo : toFiniteCWModelSix.cellCount 2 = 4
  cellsThree : toFiniteCWModelSix.cellCount 3 = 2
  cellsFour : toFiniteCWModelSix.cellCount 4 = 1
  cellsFive : toFiniteCWModelSix.cellCount 5 = 0
  cellsSix : toFiniteCWModelSix.cellCount 6 = 0

namespace CuspToricCellModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : CuspToricCellModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCWModelSix.integralHomologyFiniteSix

/-- The toric cusp cell decomposition has Euler characteristic two. -/
public theorem euler_eq_two (M : CuspToricCellModel X) :
    integralHomologyEulerCharacteristicSix X = 2 := by
  rw [M.toFiniteCWModelSix.eulerCharacteristic_eq_cellSum,
    M.cellsZero, M.cellsOne, M.cellsTwo, M.cellsThree, M.cellsFour,
    M.cellsFive, M.cellsSix]
  norm_num

end CuspToricCellModel

namespace Geometry.AnalyticData

open CuspPuncturedCollarBridge
open Topology.PaperEllipticFillingRadialRetraction

variable (A : AnalyticData)

/-- The exact homological information required from the regular central family. -/
public structure CentralHomologyEulerModel
    (X : Type) [TopologicalSpace X] : Prop where
  integralHomologyFiniteSix : IntegralHomologyFiniteSix X
  euler_eq_zero : integralHomologyEulerCharacteristicSix X = 0

/-- Exact geometric models still required for the seven local Section 7 spaces.  The fields are
CW decompositions, direct central homology and Euler data, explicit collar mapping-torus models,
and the already stated deformation retractions. -/
public structure LocalEulerModels where
  cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness
  orderThreeRadialChart : OrderThreeAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderThree.radius
  orderFourRadialChart : OrderFourAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderFour.radius
  centralModel : CentralHomologyEulerModel A.openEmbeddingStarData.central
  cuspCells : CuspToricCellModel
    (cuspRetraction.quotientCentralFiber A.starCuspWitness)
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
    exact M.cuspCells.integralHomologyFiniteSix.homotopyEquiv
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
    M.centralModel.euler_eq_zero M.cuspCells.euler_eq_two
    (Topology.EllipticReducedFiberMappingTorusHomology.orderThreeEuler_eq_zero A.periods)
    (Topology.EllipticReducedFiberMappingTorusHomology.orderFourEuler_eq_zero A.periods)
    (fun i ↦ (M.collarModel i).euler_eq_zero)

end LocalEulerModels

end Geometry.AnalyticData

end SphereSixComplex
