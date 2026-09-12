module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombCells

/-!
# Carrier reduction for the constructed A₂ honeycomb finite quotient

This file exposes the exact Laurent-transition equality underlying the remaining finite
same-fibres calculation.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction

/-- Equality of two projected positive square points is exactly equality through the explicit
partial Laurent transition between their affine carrier charts. -/
public theorem cellSquareProjection_eq_iff_chartChange
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice) (i j : Fin 6)
    (p q : CellSquare) :
    ((cellSquareProjection hr v (i, p) :
        constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        cellSquareProjection hr w (j, q) ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          (chartChange (cellChart v i) (cellChart w j)).source ∧
        chartChange (cellChart v i) (cellChart w j)
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  simp only [cellSquareProjection, cellSquarePoint,
    cellSquareCarrierPoint, Subtype.ext_iff]
  exact inclusion_eq_iff _ _ _ _

/-- The same carrier equality written solely in terms of the transition matrix's maximal
Laurent domain and its monomial map. -/
public theorem cellSquareProjection_eq_iff_monomial
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice) (i j : Fin 6)
    (p q : CellSquare) :
    ((cellSquareProjection hr v (i, p) :
        constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        cellSquareProjection hr w (j, q) ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i) (cellChart w j)) ∧
        monomial (transitionMatrix (cellChart v i) (cellChart w j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  rw [cellSquareProjection_eq_iff_chartChange, chartChange_source]
  rfl




end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end

end
