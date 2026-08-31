module

public import SphereSixComplex.Topology.CellularHomologyClassicalBoundary

/-!
# Cell-basis relabeling in an objectwise cellular-homology model

The objectwise classical cellular-homology interface does not normalize its free-cell bases.
This file makes the resulting change of cellular-coordinate boundary explicit.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereSixComplex

namespace IntegralCWCellularHomologyModel

variable {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]

/-- Relabel every free-cell basis of an objectwise cellular-homology model. -/
public def relabelCells (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+
      (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ)) :
    IntegralCWCellularHomologyModel Y where
  chainComplex := M.chainComplex
  cellBasis n := (e n).trans (M.cellBasis n)
  homologyEquiv := M.homologyEquiv

@[simp] public theorem relabelCells_chainComplex (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+
      (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ)) :
    (M.relabelCells e).chainComplex = M.chainComplex := rfl

@[simp] public theorem relabelCells_cellBasis (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+
      (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ)) (n : ℕ) :
    (M.relabelCells e).cellBasis n = (e n).trans (M.cellBasis n) := rfl

/-- The cellular differential written in the selected free-cell coordinates. -/
public def coordinateBoundary (M : IntegralCWCellularHomologyModel Y) (n : ℕ) :
    (Topology.CWComplex.cell (Set.univ : Set Y) n.succ →₀ ℤ) →+
      (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) :=
  (M.cellBasis n).symm.toAddMonoidHom.comp
    ((ConcreteCategory.hom (M.chainComplex.d n.succ n)).comp
      (M.cellBasis n.succ).toAddMonoidHom)

/-- Relabeling the free-cell bases conjugates the cellular-coordinate differential. -/
public theorem relabelCells_coordinateBoundary
    (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+
      (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ))
    (n : ℕ) (x : Topology.CWComplex.cell (Set.univ : Set Y) n.succ →₀ ℤ) :
    (M.relabelCells e).coordinateBoundary n x =
      (e n).symm (M.coordinateBoundary n (e n.succ x)) := by
  rfl

end IntegralCWCellularHomologyModel

end SphereSixComplex

end

end
