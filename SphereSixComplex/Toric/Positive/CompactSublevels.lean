module

public import SphereSixComplex.Toric.Positive.Quotient
import all SphereSixComplex.Cusp.FillingRadialCompactness

@[expose] public section

noncomputable section
open Function Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspCollar CuspPeriodExpansion
open CuspStraightening CuspStraighteningRetraction CuspToricPhaseAction
open CuspFillingRadialCompactness

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

theorem constructedModulus_frozenDeck (r : ℝ) (lambda : ParameterLattice)
    (p : localCarrier constructedModel r) :
    constructedLocalModulusRetraction r (frozenLocalPsiMap N constructedModel r lambda p) =
      ⟨normalizedPositiveDeckLocalMap N constructedModel r lambda
        (constructedLocalModulusRetraction r p),
        constructedPositiveDeck_mem N r lambda (constructedLocalModulusRetraction r p)⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  let x : Carrier := p.1
  change carrierModulus (carrierTorusAction (phaseEmbedding (N.phaseCoefficient lambda 0))
      (carrierFanShearFun lambda x)) =
    carrierTorusAction (normalizedCuspPositiveTwist N lambda)
      (carrierFanShearFun lambda (carrierModulus x))
  rw [carrierModulus_torusAction, carrierModulus_fanShear]
  rfl

def positiveQuotientHeight (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(PositiveQuotient W, ℝ) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  refine ⟨Quotient.lift (fun p ↦ ‖constructedModel.t p.1‖) ?_, ?_⟩
  · intro p q hpq
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hpq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
    obtain ⟨g, rfl⟩ := hpq
    change ‖constructedModel.t (normalizedPositiveDeckLocalMap N constructedModel _ _ q.1)‖ = _
    simp only [normalizedPositiveDeckLocalMap, normalizedPositiveDeckCarrierMap,
      constructedModel.t_torusAction, normalizedCuspPositiveTwist_last, Units.val_one,
      one_mul, constructedModel.fanShear_preserves_t]
  · apply Continuous.quotient_lift
    exact continuous_norm.comp (constructedModel.t_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

@[simp]
theorem positiveQuotientHeight_mk
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : constructedLocalPositivePart W.localWitness.radius) :
    positiveQuotientHeight W (Quotient.mk _ p) = ‖constructedModel.t p.1‖ := rfl

theorem positiveQuotientHeight_nonneg
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (y : PositiveQuotient W) :
    0 ≤ positiveQuotientHeight W y := by
  induction y using Quotient.inductionOn with
  | _ p => exact norm_nonneg (constructedModel.t p.1)


theorem positiveQuotientHeight_eq_zero_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (y : PositiveQuotient W) :
    positiveQuotientHeight W y = 0 ↔ y ∈ positiveQuotientCore W := by
  induction y using Quotient.inductionOn with
  | _ p =>
    rw [positiveQuotientHeight_mk, norm_eq_zero]
    exact (Set.ext_iff.mp (positiveDeck_central_preimage W) p).symm

def frozenModulusProjection (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(FrozenLocalCuspFilling N constructedModel W.localWitness.radius, PositiveQuotient W) := by
  let r := W.localWitness.radius
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
  let _ := frozenLocalCuspAction N constructedModel r
  refine ⟨Quotient.lift (fun p ↦ Quotient.mk _ (constructedLocalModulusRetraction r p)) ?_, ?_⟩
  · intro p q hpq
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hpq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
    obtain ⟨g, rfl⟩ := hpq
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨g, ?_⟩
    exact (constructedModulus_frozenDeck r (Multiplicative.toAdd g) q).symm
  · apply Continuous.quotient_lift
    exact continuous_quot_mk.comp (constructedLocalModulusRetraction r).continuous

def positiveModulusProjection (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(ActualLocalCuspFilling W, PositiveQuotient W) :=
  (frozenModulusProjection W).comp (quotientStraighteningHomeomorph W : C(_, _))

theorem positiveModulusProjection_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : ActualLocalCuspFilling W) :
    positiveQuotientHeight W (positiveModulusProjection W x) = actualLocalCuspFillingRadius W x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    change ‖constructedModel.t (constructedLocalModulusRetraction _ (pointStraightening W p))‖ = _
    rw [constructedLocalModulusRetraction_t]
    simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    change ‖constructedModel.t (constructedModel.torusAction _ p.1)‖ = _
    rw [constructedModel.t_torusAction, phaseEmbedding_apply_two]
    simp only [Units.val_one, one_mul]
    rfl

theorem positiveModulusProjection_surjective
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Surjective (positiveModulusProjection W) := by
  intro y
  induction y using Quotient.inductionOn with
  | _ p =>
    refine ⟨(quotientStraighteningHomeomorph W).symm (Quotient.mk _ p.1), ?_⟩
    change frozenModulusProjection W ((quotientStraighteningHomeomorph W)
      ((quotientStraighteningHomeomorph W).symm (Quotient.mk _ p.1))) = _
    rw [Homeomorph.apply_symm_apply]
    change Quotient.mk _ (constructedLocalModulusRetraction _ p.1) = _
    rw [constructedLocalModulusRetraction_fixed]

theorem isCompact_positiveQuotientHeight_sublevel
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : ℝ) (ha : 0 ≤ a) (har : a < W.localWitness.radius) :
    IsCompact {y | positiveQuotientHeight W y ≤ a} := by
  have hcompact := actualLocalCuspFillingRadiusSublevel_isCompact W
    (radialSublevelCocompactness_of_twoChartRepresentatives _
      (actualA2TwoChartRadialSublevelRepresentatives W)) a ha har
  convert hcompact.image (positiveModulusProjection W).continuous using 1
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := positiveModulusProjection_surjective W y
    exact ⟨x, by simpa only [Set.mem_ofPred_eq, ← positiveModulusProjection_height W] using hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [Set.mem_ofPred_eq, positiveModulusProjection_height W] using hx

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
