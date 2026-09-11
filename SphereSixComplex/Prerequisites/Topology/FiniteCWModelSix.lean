module

public import SphereSixComplex.Prerequisites.Topology.IntegralHomologyEuler
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.Homotopy.Equiv
public import SphereSixComplex.Prerequisites.Topology.SectionSevenLocalEulerModelsProof

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
public theorem eulerCharacteristic_eq_cellSum (M : FiniteCWModelSix X) :
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
  finite_homology k := by
    let _ := M.topology
    let _ := M.t2
    let _ := M.cwComplex
    let _ := M.finite
    let CM := CellularHomology.normalizedModel M.Carrier
    have hfin : Finite (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
      Topology.CWComplex.FiniteType.finite_cell (C := (Set.univ : Set M.Carrier)) k
    have hX : Module.Finite ℤ (CM.chainComplex.X k) :=
      Module.Finite.equiv (CM.cellBasis k).toIntLinearEquiv
    have hhom : Module.Finite ℤ (CM.chainComplex.homology k) :=
      module_finite_homology _ k hX
    have hcar : Module.Finite ℤ (IntegralSingularHomology k M.Carrier) :=
      Module.Finite.equiv (CM.homologyEquiv k).toIntLinearEquiv
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).symm.toIntLinearEquiv
  subsingleton_homology_of_six_lt k hk := by
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
  finite_homology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finite_homology k
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k e).toIntLinearEquiv
  subsingleton_homology_of_six_lt k hk := by
    let h := hX.subsingleton_homology_of_six_lt k hk
    let eH := integralSingularHomologyEquivOfHomotopyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSix

end SphereSixComplex
