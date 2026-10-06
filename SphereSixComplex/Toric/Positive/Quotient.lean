module

public import SphereSixComplex.Toric.Phase.HoneycombReduction

/-! # The positive quotient and its central core -/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar

namespace Construction

/-- The orbit quotient of the constructed positive part at the quantitative cusp radius. -/
public abbrev PositiveQuotient
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  PolarHoneycombData.OrbitQuotient
    (constructedLocalPositivePart W.localWitness.radius)

/-- The image of the zero-height honeycomb in the constructed positive quotient. -/
public abbrev positiveQuotientCore
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (PositiveQuotient W) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  PolarHoneycombData.orbitCore
    {q : constructedLocalPositivePart W.localWitness.radius |
      constructedModel.t
        (q : localCarrier constructedModel W.localWitness.radius) = 0}

/-- The zero-height fibre is closed in the constructed positive part. -/
public theorem isClosed_positiveCentralFiber (r : ℝ) :
    IsClosed {q : constructedLocalPositivePart r |
      constructedModel.t (q : localCarrier constructedModel r) = 0} := by
  exact isClosed_singleton.preimage
    (constructedModel.t_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The zero-height fibre is saturated under the normalized positive deck action. -/
public theorem positiveDeck_central_preimage
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    PolarHoneycombData.orbitProjection
        (constructedLocalPositivePart W.localWitness.radius) ⁻¹'
      PolarHoneycombData.orbitCore
        {q : constructedLocalPositivePart W.localWitness.radius |
          constructedModel.t
            (q : localCarrier constructedModel W.localWitness.radius) = 0} =
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : localCarrier constructedModel W.localWitness.radius) = 0} := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  let central := {q : constructedLocalPositivePart W.localWitness.radius |
    constructedModel.t (q : localCarrier constructedModel W.localWitness.radius) = 0}
  have hmem (lambda : ParameterLattice)
      (q : constructedLocalPositivePart W.localWitness.radius) :
      (Multiplicative.ofAdd lambda) • q ∈ central ↔ q ∈ central := by
    change constructedModel.t
        (((Multiplicative.ofAdd lambda) • q :
          constructedLocalPositivePart W.localWitness.radius) :
          localCarrier constructedModel W.localWitness.radius) = 0 ↔
      constructedModel.t
        (q : localCarrier constructedModel W.localWitness.radius) = 0
    change constructedModel.t
        (normalizedPositiveDeckLocalMap N constructedModel W.localWitness.radius lambda
          (q : localCarrier constructedModel W.localWitness.radius)) = 0 ↔ _
    simp only [normalizedPositiveDeckLocalMap, normalizedPositiveDeckCarrierMap,
      constructedModel.t_torusAction, normalizedCuspPositiveTwist_last, Units.val_one, one_mul,
      constructedModel.fanShear_preserves_t]
  change PolarHoneycombData.orbitProjection
        (constructedLocalPositivePart W.localWitness.radius) ⁻¹'
      PolarHoneycombData.orbitCore central = central
  ext q
  constructor
  · rintro ⟨c, hc, hqc⟩
    change Quotient.mk _ c = Quotient.mk _ q at hqc
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqc
    obtain ⟨g, hg⟩ := hqc
    rw [← hg] at hc
    simpa using (hmem (Multiplicative.toAdd g) q).mp hc
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The central orbit core is closed in the positive quotient. -/
public theorem isClosed_positiveDeck_orbitCore
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsClosed (positiveQuotientCore W) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  rw [← (isQuotientMap_quotient_mk'
      (s := MulAction.orbitRel (Multiplicative ParameterLattice)
        (constructedLocalPositivePart W.localWitness.radius))).isClosed_preimage]
  change IsClosed (PolarHoneycombData.orbitProjection
      (constructedLocalPositivePart W.localWitness.radius) ⁻¹'
    PolarHoneycombData.orbitCore
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : localCarrier constructedModel W.localWitness.radius) = 0})
  rw [positiveDeck_central_preimage W]
  exact isClosed_positiveCentralFiber W.localWitness.radius

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
