module

public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.FiniteClassicalCWModel
public import SphereSixComplex.Topology.SmoothAtlasOrientation
public import SphereSixComplex.Topology.SmoothRecognition

/-!
# Dimension-controlled smooth triangulation

This file isolates the classical triangulation theorem for compact finite-dimensional smooth
manifolds and derives its elementary integral-homology consequences from cellular homology.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Manifold ContinuousMap

namespace SphereSixComplex

/-- A homotopy model by a finite Hausdorff CW complex of dimension at most `d`. -/
public structure FiniteCWModelOfDimension
    (d : ℕ) (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : let _ := topology; T2Space Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)
  cellsAboveDimension : let _ := topology; let _ := cwComplex
    ∀ n, d < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Carrier) n)

/-- Every compact second-countable Hausdorff finite-dimensional boundaryless real `C¹` manifold
has the homotopy type of a finite CW complex of dimension at most the dimension of its model
space.  This is the classical smooth triangulation theorem. -/
public axiom compactCOneManifoldFiniteCWModelAtDimension
    (E X : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace E X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℝ E) 1 X)
    (hCompact : CompactSpace X) :
    FiniteCWModelOfDimension (Module.finrank ℝ E) X

namespace FiniteCWModelOfDimension

variable {d : ℕ} {X : Type} [TopologicalSpace X]

/-- Forget the dimension bound on a finite CW model. -/
public noncomputable def toFiniteCWModel (M : FiniteCWModelOfDimension d X) :
    FiniteCWModel X where
  Carrier := M.Carrier
  topology := M.topology
  t2 := M.t2
  homotopyEquiv := M.homotopyEquiv
  cwComplex := M.cwComplex
  finite := M.finite

/-- Integral homology of a space with a finite CW model is finitely generated in every degree. -/
public theorem finiteHomology (M : FiniteCWModelOfDimension d X) (k : ℕ) :
    Module.Finite ℤ (IntegralSingularHomology k X) := by
  let _ := M.topology
  let _ := M.t2
  let _ := M.cwComplex
  let _ := M.finite
  let CM := EstablishedCellularHomology.integralCWCellularHomologyModel M.Carrier
  have hfin : Finite (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
    Topology.CWComplex.FiniteType.finite_cell (C := (Set.univ : Set M.Carrier)) k
  have hChains : Module.Finite ℤ (CM.chainComplex.X k) :=
    Module.Finite.equiv (CM.cellBasis k).toIntLinearEquiv
  have hCellular : Module.Finite ℤ (CM.chainComplex.homology k) :=
    module_finite_homology _ k hChains
  have hCarrier : Module.Finite ℤ (IntegralSingularHomology k M.Carrier) :=
    Module.Finite.equiv (CM.homologyEquiv k).toIntLinearEquiv
  exact Module.Finite.equiv
    (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).symm.toIntLinearEquiv

/-- Integral homology vanishes above the dimension of a dimension-controlled finite CW model. -/
public theorem homologyAboveDimension (M : FiniteCWModelOfDimension d X) (k : ℕ) (hk : d < k) :
    Subsingleton (IntegralSingularHomology k X) := by
  let _ := M.topology
  let _ := M.t2
  let _ := M.cwComplex
  have _ : IsEmpty (Topology.CWComplex.cell (Set.univ : Set M.Carrier) k) :=
    M.cellsAboveDimension k hk
  have hCarrier := subsingleton_integralSingularHomology_of_isEmpty_cell M.Carrier k
  exact ⟨fun x y ↦
    (integralSingularHomologyEquivOfHomotopyEquiv k M.homotopyEquiv).injective
      (@Subsingleton.elim _ hCarrier _ _)⟩

end FiniteCWModelOfDimension

end SphereSixComplex

end

end
