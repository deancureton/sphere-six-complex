module

public import SphereSixComplex.Geometry.ComplexTorus
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Finite CW type of compact manifolds

This module isolates the classical compact-manifold finite-CW theorem in the real dimension used
by the elliptic surface construction.  The covering formulation includes the standard descent of
topological manifold charts along a surjective covering.
-/

@[expose] public section

noncomputable section

open SphereSixComplex.Geometry.ComplexTorus
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EstablishedCompactManifoldFiniteCW

/-- A homotopy model by a finite CW complex of dimension at most `d`. -/
public structure FiniteCWModelAtMost (d : ℕ) (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : let _ := topology; T2Space Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)
  cellsAbove : let _ := topology; let _ := cwComplex
    ∀ n, d < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Carrier) n)

/-- Forget a sharper dimension bound when constructing a model supported through degree six. -/
public noncomputable def FiniteCWModelAtMost.toFiniteCWModelSix
    {d : ℕ} {X : Type} [TopologicalSpace X] (M : FiniteCWModelAtMost d X) (hd : d ≤ 6) :
    SphereSixComplex.FiniteCWModelSix X where
  Carrier := M.Carrier
  topology := M.topology
  t2 := M.t2
  homotopyEquiv := M.homotopyEquiv
  cwComplex := M.cwComplex
  finite := M.finite
  cellsAboveSix n hn := M.cellsAbove n (hd.trans_lt hn)

/-- A compact topological complex surface has finite CW homotopy type, of real dimension at most
four, and so does the Hausdorff base of any surjective covering from it. -/
public axiom establishedFiniteCWModelFour_of_compactComplexSurfaceCover
    {E X : Type} [TopologicalSpace E] [ChartedSpace ComplexTwoSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    (_hManifold : IsManifold (modelWithCornersSelf ℂ ComplexTwoSpace) 0 E)
    (_hcompact : CompactSpace E)
    (projection : C(E, X)) (_hcover : IsCoveringMap projection)
    (_hsurjective : Function.Surjective projection) :
    FiniteCWModelAtMost 4 X

end SphereSixComplex.Topology.EstablishedCompactManifoldFiniteCW

end

end
