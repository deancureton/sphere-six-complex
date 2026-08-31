module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCellDataProof

/-!
# Carrier reduction for the constructed A₂ honeycomb finite quotient

This file exposes the exact Laurent-transition equality underlying the remaining finite
same-fibres calculation.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

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

/-- The exact finite equality still needed after reducing carrier equality to explicit Laurent
coordinates. -/
public def ConstructedA2HoneycombLaurentFiniteIdentity : Prop :=
  ∀ v w i j p q,
    constructedA2PlaneTile v i p = constructedA2PlaneTile w j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))

/-- The Laurent finite identity is precisely sufficient for the requested quotient residual. -/
public theorem constructedA2HoneycombFiniteQuotientResidual_of_laurentFiniteIdentity
    {r : ℝ} (hr : 0 < r) (H : ConstructedA2HoneycombLaurentFiniteIdentity) :
    ConstructedA2HoneycombFiniteQuotientResidual r hr where
  sameFibres := by
    intro v w a b
    rcases a with ⟨i, p⟩
    rcases b with ⟨j, q⟩
    change constructedA2PlaneTile v i p = constructedA2PlaneTile w j q ↔ _
    rw [H v w i j p q]
    exact (constructedA2CellSquareProjection_eq_iff_monomial hr v w i j p q).symm

/-- There is no further quotient-topology obstruction: the residual exists exactly when the
displayed Laurent finite identity holds. -/
public theorem nonempty_constructedA2HoneycombFiniteQuotientResidual_iff
    {r : ℝ} (hr : 0 < r) :
    Nonempty (ConstructedA2HoneycombFiniteQuotientResidual r hr) ↔
      ConstructedA2HoneycombLaurentFiniteIdentity := by
  constructor
  · rintro ⟨H⟩ v w i j p q
    have h := H.sameFibres v w (i, p) (j, q)
    change constructedA2PlaneTile v i p = constructedA2PlaneTile w j q ↔ _ at h
    exact h.trans (constructedA2CellSquareProjection_eq_iff_monomial hr v w i j p q)
  · exact fun H ↦ ⟨constructedA2HoneycombFiniteQuotientResidual_of_laurentFiniteIdentity hr H⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
