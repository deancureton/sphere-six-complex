module

public import SphereSixComplex.Toric.Positive.Quotient
public import SphereSixComplex.Toric.Honeycomb.Cells

/-!
# Compactness of the positive quotient core

Every central deck orbit meets the compact cell over the zero ray.
-/

@[expose] public section

open Function Set Topology
noncomputable section
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem isCompact_positiveQuotientCore
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsCompact (positiveQuotientCore W) := by
  let r := W.localWitness.radius
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
  let π := PolarHoneycombData.orbitProjection (constructedLocalPositivePart r)
  let F : Fin 6 × CellSquare → PositiveQuotient W :=
    fun p ↦ π (cellSquareProjection W.localWitness.radius_pos 0 p).1.1
  have hF : Continuous F := π.continuous.comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_cellSquareProjection W.localWitness.radius_pos 0)))
  have hcover : range F = positiveQuotientCore W := by
    apply Subset.antisymm
    · rintro _ ⟨p, rfl⟩
      exact ⟨(cellSquareProjection W.localWitness.radius_pos 0 p).1.1,
        (cellSquareProjection W.localWitness.radius_pos 0 p).1.2, rfl⟩
    · rintro x ⟨q, hq, rfl⟩
      obtain ⟨v, hv⟩ := componentSupport_nonempty_of_t_eq_zero constructedModel hq
      obtain ⟨lambda, hlambda⟩ := shearVector_surjective (-v)
      let g := Multiplicative.ofAdd lambda
      let q' : constructedLocalPositivePart r := g • q
      have hq' : constructedModel.t (q' : localCarrier constructedModel r) = 0 := by
        change constructedModel.t (normalizedPositiveDeckLocalMap N constructedModel r lambda q) = 0
        simp only [normalizedPositiveDeckLocalMap, normalizedPositiveDeckCarrierMap,
          constructedModel.t_torusAction, normalizedCuspPositiveTwist_last, Units.val_one,
          one_mul, constructedModel.fanShear_preserves_t]
        exact hq
      have hv' : (q'.1.1 : Carrier) ∈ carrierCentralComponent 0 := by
        change constructedModel.torusAction (normalizedCuspPositiveTwist N lambda)
          (Additive.toMul (constructedModel.fanShear lambda) (q.1.1 : Carrier)) ∈
          constructedModel.centralComponent 0
        rw [constructedModel.torusAction_centralComponent]
        have hs : Additive.toMul (constructedModel.fanShear lambda) (q.1.1 : Carrier) ∈
            constructedModel.centralComponent (v + shearVector lambda) := by
          rw [← constructedModel.fanShear_component lambda v]
          exact ⟨q.1.1, hv, rfl⟩
        simpa [hlambda] using hs
      let z : constructedPositiveCentralCell r 0 := ⟨⟨q', hq'⟩, hv'⟩
      obtain ⟨p, hp⟩ := surjective_cellSquareProjection W.localWitness.radius_pos 0 z
      refine ⟨p, ?_⟩
      change π (cellSquareProjection W.localWitness.radius_pos 0 p).1.1 = π q
      rw [hp]
      apply Quotient.sound
      change MulAction.orbitRel (Multiplicative ParameterLattice) _ q' q
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, rfl⟩
  rw [← hcover]
  exact isCompact_range hF

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
