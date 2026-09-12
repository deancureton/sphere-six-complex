module

public import SphereSixComplex.Paper.Topology.ConstructedPositiveLogCoordinates

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open Set Topology
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods CuspFilling CuspLocalPhaseAction CuspCollar
open CuspPeriodExpansion InfiniteA2Toric.Construction
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def constructedPositiveInteriorProjection
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : positiveOffCentral W.localWitness.radius) :
    ↥((positiveQuotientCore W)ᶜ) := by
  refine ⟨Quotient.mk _ p.1, ?_⟩
  have h := Set.ext_iff.mp (positiveDeck_central_preimage W) p.1
  exact fun hp ↦ p.2 (h.mp hp)

theorem constructedPositiveInteriorProjection_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedPositiveInteriorProjection W) :=
  (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _

theorem constructedPositiveInteriorProjection_surjective
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Function.Surjective (constructedPositiveInteriorProjection W) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  have hp : constructedModel.t p.1.1 ≠ 0 := by
    have h := Set.ext_iff.mp (positiveDeck_central_preimage W) p
    exact fun hp ↦ hx (h.mpr hp)
  exact ⟨⟨p, hp⟩, rfl⟩

theorem constructedPositiveInteriorProjection_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : positiveOffCentral W.localWitness.radius) :
    constructedPositiveInteriorProjection W p = constructedPositiveInteriorProjection W q ↔
      ∃ lambda : ParameterLattice, positiveOffCentralDeck W lambda q = p := by
  rw [Subtype.ext_iff]
  change Quotient.mk _ p.1 = Quotient.mk _ q.1 ↔ _
  rw [Quotient.eq]
  change (∃ g : Multiplicative ParameterLattice,
    (normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)).smul g q.1 = p.1) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.toAdd, Subtype.ext hg⟩
  · rintro ⟨lambda, h⟩
    exact ⟨Multiplicative.ofAdd lambda, congrArg Subtype.val h⟩

theorem constructedPositiveInteriorProjection_isOpenMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsOpenMap (constructedPositiveInteriorProjection W) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  have h : IsOpen (positiveOffCentral W.localWitness.radius) :=
    (isClosed_positiveCentralFiber W.localWitness.radius).isOpen_compl
  exact ((constructedPositiveDeck_quotientCovering W).isCoveringMap.isLocalHomeomorph.isOpenMap.comp
    h.isOpenMap_subtype_val).subtype_mk _

theorem constructedPositiveInteriorProjection_isQuotientMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsQuotientMap (constructedPositiveInteriorProjection W) :=
  (constructedPositiveInteriorProjection_isOpenMap W).isQuotientMap
    (constructedPositiveInteriorProjection_continuous W)
    (constructedPositiveInteriorProjection_surjective W)

end SphereSixComplex.Geometry.InfiniteA2Toric
