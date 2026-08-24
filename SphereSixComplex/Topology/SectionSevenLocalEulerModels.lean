module

public import SphereSixComplex.Topology.SectionSevenLocalEulerCalculation
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Finite CW models for the Section 7 local Euler calculation

This file states the missing general Euler--Poincaré, fibre-bundle, and finite-cover theorems at
their natural finite-CW level.  It then reduces the seven local values to geometric CW, bundle, and
covering models.  The resulting Section 7 contract contains no homology ranks and no Euler values.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- A homotopy model by a finite CW complex of dimension at most six. -/
public structure FiniteCWModelSix (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)
  cellsAboveSix : let _ := topology; let _ := cwComplex
    ∀ n, 6 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Carrier) n)

namespace FiniteCWModelSix

variable {X : Type} [TopologicalSpace X]

/-- Number of cells in one degree of the chosen finite CW model. -/
public noncomputable def cellCount (M : FiniteCWModelSix X) (n : ℕ) : ℕ := by
  let _ := M.topology
  let _ := M.cwComplex
  let _ := M.finite
  exact Nat.card (Topology.CWComplex.cell (Set.univ : Set M.Carrier) n)

/-- Cellular Euler--Poincaré over the integers, including finite generation of homology.

Mathlib has finite CW complexes and singular homology, but currently has no cellular homology or
Euler--Poincaré comparison theorem joining these APIs. -/
public axiom establishedIntegralCellularEulerPoincareSix (M : FiniteCWModelSix X) :
    IntegralHomologyFiniteSix X ∧
      integralHomologyEulerCharacteristicSix X =
        (M.cellCount 0 : ℤ) - M.cellCount 1 + M.cellCount 2 - M.cellCount 3 +
          M.cellCount 4 - M.cellCount 5 + M.cellCount 6

public theorem integralHomologyFiniteSix (M : FiniteCWModelSix X) :
    IntegralHomologyFiniteSix X :=
  M.establishedIntegralCellularEulerPoincareSix.1

end FiniteCWModelSix

namespace IntegralHomologyFiniteSix

/-- Homological finiteness and the dimension bound transport through a homotopy equivalence. -/
public theorem homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IntegralHomologyFiniteSix X) (e : X ≃ₕ Y) : IntegralHomologyFiniteSix Y where
  finiteHomology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finiteHomology k
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k e).toIntLinearEquiv
  homologyAboveDimension k hk := by
    let h := hX.homologyAboveDimension k hk
    let eH := integralSingularHomologyEquivOfHomotopyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSix

/-- The standard product CW structure on a four-torus has cell counts `1, 4, 6, 4, 1`.
This structure asks for that geometric CW model, not for its homology or Euler characteristic. -/
public structure FourTorusCellModel (X : Type) [TopologicalSpace X] where
  toFiniteCWModelSix : FiniteCWModelSix X
  cellsZero : toFiniteCWModelSix.cellCount 0 = 1
  cellsOne : toFiniteCWModelSix.cellCount 1 = 4
  cellsTwo : toFiniteCWModelSix.cellCount 2 = 6
  cellsThree : toFiniteCWModelSix.cellCount 3 = 4
  cellsFour : toFiniteCWModelSix.cellCount 4 = 1
  cellsFive : toFiniteCWModelSix.cellCount 5 = 0
  cellsSix : toFiniteCWModelSix.cellCount 6 = 0

namespace FourTorusCellModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : FourTorusCellModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCWModelSix.integralHomologyFiniteSix

/-- Euler characteristic zero is derived from the standard four-torus cell counts. -/
public theorem euler_eq_zero (M : FourTorusCellModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  rw [M.toFiniteCWModelSix.establishedIntegralCellularEulerPoincareSix.2,
    M.cellsZero, M.cellsOne, M.cellsTwo, M.cellsThree, M.cellsFour,
    M.cellsFive, M.cellsSix]
  norm_num

end FourTorusCellModel

/-- A finite-CW locally trivial bundle model for a space. -/
public structure FiniteCWBundleModelSix (X : Type) [TopologicalSpace X] where
  Base : Type
  Fiber : Type
  baseTopology : TopologicalSpace Base
  fiberTopology : TopologicalSpace Fiber
  family : Base → Type
  familyTopology : ∀ b, TopologicalSpace (family b)
  totalTopology : TopologicalSpace (Bundle.TotalSpace Fiber family)
  fiberBundle : @FiberBundle Base Fiber baseTopology fiberTopology family totalTopology
    familyTopology
  totalHomotopyEquiv : let _ := baseTopology; let _ := fiberTopology
    let _ := familyTopology; let _ := totalTopology
    X ≃ₕ Bundle.TotalSpace Fiber family
  baseFiniteCW : @FiniteCWModelSix Base baseTopology
  fiberFiniteCW : @FiniteCWModelSix Fiber fiberTopology
  totalFiniteCW : @FiniteCWModelSix (Bundle.TotalSpace Fiber family) totalTopology

namespace FiniteCWBundleModelSix

variable {X : Type} [TopologicalSpace X]

/-- Euler characteristic is multiplicative for a locally trivial bundle of finite CW complexes.
This is the standard Serre-spectral-sequence Euler theorem missing from Mathlib. -/
public axiom establishedEulerMultiplicativity (M : FiniteCWBundleModelSix X) :
    let _ := M.baseTopology
    let _ := M.fiberTopology
    integralHomologyEulerCharacteristicSix X =
      integralHomologyEulerCharacteristicSix M.Base *
        integralHomologyEulerCharacteristicSix M.Fiber

public theorem integralHomologyFiniteSix (M : FiniteCWBundleModelSix X) :
    IntegralHomologyFiniteSix X := by
  let _ := M.baseTopology
  let _ := M.fiberTopology
  let _ := M.familyTopology
  let _ := M.totalTopology
  exact M.totalFiniteCW.integralHomologyFiniteSix.homotopyEquiv M.totalHomotopyEquiv.symm

end FiniteCWBundleModelSix

/-- A finite-CW bundle whose model fibre has the standard four-torus CW structure. -/
public structure FourTorusBundleModel (X : Type) [TopologicalSpace X] where
  toFiniteCWBundleModelSix : FiniteCWBundleModelSix X
  fiberCells : @FourTorusCellModel toFiniteCWBundleModelSix.Fiber
    toFiniteCWBundleModelSix.fiberTopology

namespace FourTorusBundleModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : FourTorusBundleModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCWBundleModelSix.integralHomologyFiniteSix

/-- Every finite-CW bundle with four-torus fibre has Euler characteristic zero. -/
public theorem euler_eq_zero (M : FourTorusBundleModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  let _ := M.toFiniteCWBundleModelSix.baseTopology
  let _ := M.toFiniteCWBundleModelSix.fiberTopology
  rw [M.toFiniteCWBundleModelSix.establishedEulerMultiplicativity,
    M.fiberCells.euler_eq_zero, mul_zero]

end FourTorusBundleModel

/-- A constant-degree finite covering between finite CW-type spaces. -/
public structure FiniteCoverModelSix (X : Type) [TopologicalSpace X] where
  Cover : Type
  coverTopology : TopologicalSpace Cover
  projection : let _ := coverTopology; C(Cover, X)
  isCovering : let _ := coverTopology; IsCoveringMap projection
  degree : ℕ
  degree_pos : 0 < degree
  fiberCardinality : let _ := coverTopology
    ∀ x, Nat.card {y : Cover // projection y = x} = degree
  coverFiniteCW : @FiniteCWModelSix Cover coverTopology
  quotientFiniteCW : FiniteCWModelSix X

namespace FiniteCoverModelSix

variable {X : Type} [TopologicalSpace X]

/-- Euler characteristic multiplies by the degree of a finite covering. -/
public axiom establishedEulerMultiplicativity (M : FiniteCoverModelSix X) :
    let _ := M.coverTopology
    integralHomologyEulerCharacteristicSix M.Cover =
      (M.degree : ℤ) * integralHomologyEulerCharacteristicSix X

end FiniteCoverModelSix

/-- A finite quotient of a four-torus, expressed by its actual finite covering projection. -/
public structure FiniteFourTorusCoverModel (X : Type) [TopologicalSpace X] where
  toFiniteCoverModelSix : FiniteCoverModelSix X
  coverCells : @FourTorusCellModel toFiniteCoverModelSix.Cover
    toFiniteCoverModelSix.coverTopology

namespace FiniteFourTorusCoverModel

variable {X : Type} [TopologicalSpace X]

public theorem integralHomologyFiniteSix (M : FiniteFourTorusCoverModel X) :
    IntegralHomologyFiniteSix X :=
  M.toFiniteCoverModelSix.quotientFiniteCW.integralHomologyFiniteSix

/-- A finite free quotient of a four-torus has Euler characteristic zero. -/
public theorem euler_eq_zero (M : FiniteFourTorusCoverModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  let _ := M.toFiniteCoverModelSix.coverTopology
  have h := M.toFiniteCoverModelSix.establishedEulerMultiplicativity
  dsimp only at h
  rw [M.coverCells.euler_eq_zero] at h
  have hdegree : (M.toFiniteCoverModelSix.degree : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.toFiniteCoverModelSix.degree_pos)
  exact (mul_eq_zero.mp h.symm).resolve_left hdegree

end FiniteFourTorusCoverModel

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
  rw [M.toFiniteCWModelSix.establishedIntegralCellularEulerPoincareSix.2,
    M.cellsZero, M.cellsOne, M.cellsTwo, M.cellsThree, M.cellsFour,
    M.cellsFive, M.cellsSix]
  norm_num

end CuspToricCellModel

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open Topology.PaperEllipticFillingRadialRetraction

variable (A : PaperAnalyticData)

/-- Exact geometric models still required for the seven local Section 7 spaces.  The fields are
CW decompositions, locally trivial bundles, finite covering projections, and the already stated
deformation retractions; no field stores a homology rank or Euler characteristic. -/
public structure SectionSevenLocalEulerModels where
  cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness
  orderThreeRadialChart : OrderThreeAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderThree.radius
  orderFourRadialChart : OrderFourAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderFour.radius
  centralBundle : FourTorusBundleModel A.openEmbeddingStarData.central
  cuspCells : CuspToricCellModel
    (cuspRetraction.quotientCentralFiber A.starCuspWitness)
  orderThreeCover : FiniteFourTorusCoverModel
    (OrderThreeReducedCentralFiber A.periods)
  orderFourCover : FiniteFourTorusCoverModel
    (OrderFourReducedCentralFiber A.periods)
  collarBundle : ∀ i : Fin 3, FourTorusBundleModel
    (A.openEmbeddingStarData.collarSource i)

namespace SectionSevenLocalEulerModels

/-- All seven local spaces have finite integral homology supported in degrees at most six. -/
public theorem localIntegralHomologyFiniteSix (M : SectionSevenLocalEulerModels A) :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.filling i)) ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource i)) := by
  refine ⟨M.centralBundle.integralHomologyFiniteSix, ?_, fun i ↦
    (M.collarBundle i).integralHomologyFiniteSix⟩
  intro i
  fin_cases i
  · change IntegralHomologyFiniteSix (actualLocalCuspFilling A.starCuspWitness)
    exact M.cuspCells.integralHomologyFiniteSix.homotopyEquiv
      (M.cuspRetraction.quotientCentralFiberHomotopyEquiv A.starCuspWitness).symm
  · change IntegralHomologyFiniteSix
      (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
    exact M.orderThreeCover.integralHomologyFiniteSix.homotopyEquiv
      (orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
        A.starSeparation.orderThree.radius M.orderThreeRadialChart).symm
  · change IntegralHomologyFiniteSix
      (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)
    exact M.orderFourCover.integralHomologyFiniteSix.homotopyEquiv
      (orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
        A.starSeparation.orderFour.radius M.orderFourRadialChart).symm

/-- The exact Section 7 local Euler calculation, derived from geometric models. -/
public theorem sectionSevenLocalEulerExpression_eq_two (M : SectionSevenLocalEulerModels A) :
    A.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2 :=
  A.sectionSevenLocalEulerExpression_eq_two_of_modelCalculations
    M.cuspRetraction M.orderThreeRadialChart M.orderFourRadialChart
    M.centralBundle.euler_eq_zero M.cuspCells.euler_eq_two
    M.orderThreeCover.euler_eq_zero M.orderFourCover.euler_eq_zero
    (fun i ↦ (M.collarBundle i).euler_eq_zero)

end SectionSevenLocalEulerModels

end Geometry.PaperAnalyticData

end SphereSixComplex
