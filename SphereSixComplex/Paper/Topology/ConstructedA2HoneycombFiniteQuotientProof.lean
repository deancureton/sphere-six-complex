module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCellDataProof

/-!
# Carrier reduction for the constructed A₂ honeycomb finite quotient

This file exposes the exact Laurent-transition equality underlying the remaining finite
same-fibres calculation.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

/-- Equality of two projected positive square points is exactly equality through the explicit
partial Laurent transition between their affine carrier charts. -/
public theorem constructedA2CellSquareProjection_eq_iff_chartChange
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice) (i j : Fin 6)
    (p q : ConstructedA2CellSquare) :
    ((constructedA2CellSquareProjection hr v (i, p) :
        constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        constructedA2CellSquareProjection hr w (j, q) ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          (chartChange (constructedA2CellChart v i) (constructedA2CellChart w j)).source ∧
        chartChange (constructedA2CellChart v i) (constructedA2CellChart w j)
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  simp only [constructedA2CellSquareProjection, constructedA2CellSquarePoint,
    constructedA2CellSquareCarrierPoint, Subtype.ext_iff]
  exact inclusion_eq_iff _ _ _ _

/-- The same carrier equality written solely in terms of the transition matrix's maximal
Laurent domain and its monomial map. -/
public theorem constructedA2CellSquareProjection_eq_iff_monomial
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice) (i j : Fin 6)
    (p q : ConstructedA2CellSquare) :
    ((constructedA2CellSquareProjection hr v (i, p) :
        constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        constructedA2CellSquareProjection hr w (j, q) ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CellSquareProjection_eq_iff_chartChange, chartChange_source]
  rfl




end SphereSixComplex.Geometry.InfiniteA2Toric

end

end
