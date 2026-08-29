module

public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.FiniteBouquetMappingTorusEuler
public import SphereSixComplex.Topology.SectionSevenLocalEulerCalculation
public import SphereSixComplex.Topology.SectionSevenLocalEulerModelsProof
public import SphereSixComplex.Topology.StandardFourTorusHomologicalModel
public import Mathlib.Topology.CWComplex.Classical.Finite

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

/-- A homotopy model by a finite CW complex of dimension at most six. -/
public structure FiniteCWModelSix (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  /-- The carrier is Hausdorff.  `Topology.CWComplex` carries no separation axiom, and the
  cellular chain model is false without one; see
  `SphereSixComplex.isEmpty_forall_integralCWCellularChainModel`. -/
  t2 : let _ := topology; T2Space Carrier
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

/-- Cellular Euler--Poincaré over the integers.

Reference: [Hat02, Theorem 2.44] (the Euler characteristic equals the alternating sum of the cell
counts).  Truncating the sum at degree six is sound because `FiniteCWModelSix` records that there
are no cells above degree six.  The proof is the rank bookkeeping of
`CellularEulerPoincare.integralHomologyEulerCharacteristicSix_eq_cellSum` on the cellular chain
complex of the chosen carrier. -/
public theorem establishedIntegralCellularEulerPoincareSix (M : FiniteCWModelSix X) :
    integralHomologyEulerCharacteristicSix X =
      (M.cellCount 0 : ℤ) - M.cellCount 1 + M.cellCount 2 - M.cellCount 3 +
        M.cellCount 4 - M.cellCount 5 + M.cellCount 6 := by
  let _ := M.topology
  let _ := M.t2
  let _ := M.cwComplex
  let _ := M.finite
  exact CellularEulerPoincare.integralHomologyEulerCharacteristicSix_eq_cellSum
    M.homotopyEquiv M.cellsAboveSix

/-- Finite generation and the dimension bound are consequences of the cellular chain model, not
extra assumptions: the chain groups are free on finitely many cells, homology is a subquotient of
them, and there are no cells above degree six. -/
public theorem integralHomologyFiniteSix (M : FiniteCWModelSix X) :
    IntegralHomologyFiniteSix X where
  finiteHomology k := by
    let _ := M.topology
    let _ := M.t2
    let _ := M.cwComplex
    let _ := M.finite
    let CM := EstablishedCellularHomology.integralCWCellularChainModel M.Carrier
    have hfin : Finite (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
      Topology.CWComplex.FiniteType.finite_cell (C := (Set.univ : Set M.Carrier)) k
    have hX : Module.Finite ℤ (CM.chainComplex.X k) :=
      Module.Finite.equiv (CM.cellBasis k).toIntLinearEquiv
    have hhom : Module.Finite ℤ (CM.chainComplex.homology k) :=
      module_finite_homology _ k hX
    have hiso := CM.comparison_homology_isIso k
    have hcar : Module.Finite ℤ (IntegralSingularHomology k M.Carrier) :=
      Module.Finite.equiv (asIso (CM.chainComplex.homologyMap CM.comparison k)
        |>.addCommGroupIsoToAddEquiv).toIntLinearEquiv
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).symm.toIntLinearEquiv
  homologyAboveDimension k hk := by
    let _ := M.topology
    let _ := M.t2
    let _ := M.cwComplex
    have _hempty : IsEmpty (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
      M.cellsAboveSix k hk
    have _hcar := subsingleton_integralSingularHomology_of_isEmpty_cell M.Carrier k
    exact ⟨fun _ _ =>
      (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).injective
        (Subsingleton.elim _ _)⟩

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

/-- A homotopy model by a finite CW complex, with no dimension bound. -/
public structure FiniteCWModel (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : let _ := topology; T2Space Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)

namespace FiniteCWModel

variable {X : Type} [TopologicalSpace X]

/-- Number of cells in one degree of the chosen finite CW model. -/
public noncomputable def cellCount (M : FiniteCWModel X) (n : ℕ) : ℕ := by
  let _ := M.topology
  let _ := M.cwComplex
  let _ := M.finite
  exact Nat.card (Topology.CWComplex.cell (Set.univ : Set M.Carrier) n)

end FiniteCWModel

namespace FiniteCWModelSix

/-- Forget the dimension bound on a finite CW model. -/
public noncomputable def toFiniteCWModel {X : Type} [TopologicalSpace X]
    (M : FiniteCWModelSix X) : FiniteCWModel X where
  Carrier := M.Carrier
  topology := M.topology
  t2 := M.t2
  homotopyEquiv := M.homotopyEquiv
  cwComplex := M.cwComplex
  finite := M.finite

@[simp]
public theorem toFiniteCWModel_cellCount {X : Type} [TopologicalSpace X]
    (M : FiniteCWModelSix X) (n : ℕ) : M.toFiniteCWModel.cellCount n = M.cellCount n := rfl

end FiniteCWModelSix

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
  coverHomologyFiniteSix : @IntegralHomologyFiniteSix Cover coverTopology
  quotientFiniteCW : FiniteCWModelSix X

/-- A finite-sheeted covering of a space of finite CW type has finite CW type.  The CW structure
can be chosen by lifting the cells, so in every degree each base cell has one lift for each point
of a fibre. -/
public axiom establishedFiniteCoverCellularLift
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (projection : C(E, X)) (_isCovering : IsCoveringMap projection)
    (degree : ℕ) (_fiberCardinality : ∀ x, Nat.card {y : E // projection y = x} = degree)
    (base : FiniteCWModel X) :
    ∃ cover : FiniteCWModel E, ∀ n, cover.cellCount n = degree * base.cellCount n

/-- Pulling a constant finite-sheeted cover back along a finite CW homotopy model of its base and
lifting the cells gives a finite CW homotopy model of the cover.  In every degree, each base cell
has one lift for each point of a fibre. -/
public theorem establishedFiniteCoverCellularLiftSix
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (projection : C(E, X)) (_isCovering : IsCoveringMap projection)
    (degree : ℕ) (_fiberCardinality : ∀ x, Nat.card {y : E // projection y = x} = degree)
    (base : FiniteCWModelSix X) :
    ∃ cover : FiniteCWModelSix E, ∀ n, cover.cellCount n = degree * base.cellCount n := by
  obtain ⟨cover, hcells⟩ := establishedFiniteCoverCellularLift projection _isCovering degree
    _fiberCardinality base.toFiniteCWModel
  let coverSix : FiniteCWModelSix E := {
    Carrier := cover.Carrier
    topology := cover.topology
    t2 := cover.t2
    homotopyEquiv := cover.homotopyEquiv
    cwComplex := cover.cwComplex
    finite := cover.finite
    cellsAboveSix := by
      dsimp only
      intro n hn
      let _ := cover.topology
      let _ := cover.cwComplex
      let _ := cover.finite
      have hfinite : Finite (Topology.CWComplex.cell
          (Set.univ : Set cover.Carrier) n) :=
        Topology.CWComplex.FiniteType.finite_cell
          (C := (Set.univ : Set cover.Carrier)) n
      let _ := hfinite
      apply Finite.card_eq_zero_iff.mp
      change cover.cellCount n = 0
      rw [hcells n]
      rw [mul_eq_zero]
      right
      rw [FiniteCWModelSix.toFiniteCWModel_cellCount]
      unfold FiniteCWModelSix.cellCount
      let _ := base.topology
      let _ := base.cwComplex
      let _ := base.cellsAboveSix n hn
      exact Nat.card_of_isEmpty }
  refine ⟨coverSix, fun n ↦ ?_⟩
  exact hcells n

namespace FiniteCoverModelSix

variable {X : Type} [TopologicalSpace X]

/-- Euler characteristic multiplies by the constant sheet number of a finite covering between
spaces of finite integral homology type. -/
public theorem establishedEulerMultiplicativity (M : FiniteCoverModelSix X) :
    let _ := M.coverTopology
    integralHomologyEulerCharacteristicSix M.Cover =
      (M.degree : ℤ) * integralHomologyEulerCharacteristicSix X := by
  let _ := M.coverTopology
  dsimp only
  obtain ⟨cover, hcells⟩ := establishedFiniteCoverCellularLiftSix M.projection M.isCovering
    M.degree M.fiberCardinality M.quotientFiniteCW
  rw [cover.establishedIntegralCellularEulerPoincareSix,
    M.quotientFiniteCW.establishedIntegralCellularEulerPoincareSix]
  rw [hcells 0, hcells 1, hcells 2, hcells 3, hcells 4, hcells 5, hcells 6]
  push_cast
  ring

end FiniteCoverModelSix

/-- A finite quotient of a four-torus, expressed by its actual finite covering projection. -/
public structure FiniteFourTorusCoverModel (X : Type) [TopologicalSpace X] where
  toFiniteCoverModelSix : FiniteCoverModelSix X
  coverHomology : @FourTorusHomologicalModel toFiniteCoverModelSix.Cover
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
  rw [M.coverHomology.euler_eq_zero] at h
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
  rw [M.toFiniteCWModelSix.establishedIntegralCellularEulerPoincareSix,
    M.cellsZero, M.cellsOne, M.cellsTwo, M.cellsThree, M.cellsFour,
    M.cellsFive, M.cellsSix]
  norm_num

end CuspToricCellModel

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open Topology.PaperEllipticFillingRadialRetraction

variable (A : PaperAnalyticData)

/-- The exact homological information required from the regular central family. -/
public structure CentralHomologyEulerModel
    (X : Type) [TopologicalSpace X] : Prop where
  integralHomologyFiniteSix : IntegralHomologyFiniteSix X
  euler_eq_zero : integralHomologyEulerCharacteristicSix X = 0

/-- Exact geometric models still required for the seven local Section 7 spaces.  The fields are
CW decompositions, direct central homology and Euler data, explicit collar mapping-torus models,
finite covering projections, and the already stated deformation retractions. -/
public structure SectionSevenLocalEulerModels where
  cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness
  orderThreeRadialChart : OrderThreeAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderThree.radius
  orderFourRadialChart : OrderFourAffineRadialWholeFillingCompatibility A
    A.starSeparation.orderFour.radius
  centralModel : CentralHomologyEulerModel A.openEmbeddingStarData.central
  cuspCells : CuspToricCellModel
    (cuspRetraction.quotientCentralFiber A.starCuspWitness)
  orderThreeCover : FiniteFourTorusCoverModel
    (OrderThreeReducedCentralFiber A.periods)
  orderFourCover : FiniteFourTorusCoverModel
    (OrderFourReducedCentralFiber A.periods)
  collarModel : ∀ i : Fin 3, FourTorusCircleMappingTorusModel
    (A.openEmbeddingStarData.collarSource i)

namespace SectionSevenLocalEulerModels

/-- All seven local spaces have finite integral homology supported in degrees at most six. -/
public theorem localIntegralHomologyFiniteSix (M : SectionSevenLocalEulerModels A) :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.filling i)) ∧
    (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource i)) := by
  refine ⟨M.centralModel.integralHomologyFiniteSix, ?_, fun i ↦
    (M.collarModel i).integralHomologyFiniteSix⟩
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
    M.centralModel.euler_eq_zero M.cuspCells.euler_eq_two
    M.orderThreeCover.euler_eq_zero M.orderFourCover.euler_eq_zero
    (fun i ↦ (M.collarModel i).euler_eq_zero)

end SectionSevenLocalEulerModels

end Geometry.PaperAnalyticData

end SphereSixComplex
