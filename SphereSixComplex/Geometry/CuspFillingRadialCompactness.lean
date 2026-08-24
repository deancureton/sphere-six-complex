module

public import SphereSixComplex.Geometry.PaperFillingCompactCores

/-!
# Compact radial cores in a toric cusp filling

Compactness of a lattice quotient is reduced to a cocompact-fundamental-domain
statement for the polarized toric degeneration.  The reduction is completely generic and the
remaining datum mentions only the toric model, its lattice action, and compact representatives.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry.CuspFillingRadialCompactness

open Set SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPeriodExpansion StandardInfiniteA2ToricModel
open StandardInfiniteA2ToricQuantitativeRegions
open CuspPhaseEstimates.CuspPeriodExpansion

noncomputable section

/-- The quotient of a local toric degeneration by a fixed-point-free phase-corrected lattice
action. -/
public noncomputable abbrev PhaseCorrectedToricQuotient
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) :=
  letI := (C.toCuspActionData F).psiAction
  MulAction.orbitRel.Quotient (Multiplicative ParameterLattice) (LocalCarrier M r)

/-- The height radius descended to a phase-corrected toric quotient. -/
@[expose] public noncomputable def phaseCorrectedQuotientRadius
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) : PhaseCorrectedToricQuotient C F → ℝ := by
  let _ := (C.toCuspActionData F).psiAction
  exact Quotient.lift (fun p : LocalCarrier M r ↦ ‖M.t p‖) (by
    intro p q hpq
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hpq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
    obtain ⟨lambda, rfl⟩ := hpq
    exact congrArg norm ((C.toCuspActionData F).preserves_t lambda q))

@[simp]
public theorem phaseCorrectedQuotientRadius_mk
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) (p : LocalCarrier M r) :
    phaseCorrectedQuotientRadius C F (Quotient.mk _ p) = ‖M.t p‖ :=
  rfl

/-- Exact cocompactness datum for a polarized toric degeneration over every closed smaller
height disc.  This is the usual compact fundamental-domain assertion for the lattice action;
it is independent of the six-sphere gluing and does not assume compactness of the quotient. -/
public structure RadialSublevelCocompactness
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r) : Prop where
  compact_fundamental_domain : ∀ a : ℝ, 0 ≤ a → a < r →
    ∃ K : Set (LocalCarrier M r), IsCompact K ∧
      K ⊆ {p | ‖M.t p‖ ≤ a} ∧
      ∀ p : LocalCarrier M r, ‖M.t p‖ ≤ a →
        ∃ lambda : ParameterLattice, C.psiMap lambda p ∈ K

/-- Concrete bounded-representative form of the required `A₂` toric cocompactness theorem.
Modulo the phase-corrected fan lattice, every point over a closed smaller height disc has a
representative in one of the two fixed affine polydiscs based at the zero vertex. -/
public structure A2TwoChartRadialSublevelRepresentatives
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r) : Prop where
  bounded_representative : ∀ a : ℝ, 0 ≤ a → a < r →
    ∃ S : ℝ, ∀ p : LocalCarrier M r, ‖M.t p‖ ≤ a →
      ∃ lambda : ParameterLattice, ∃ upper : Bool,
        (C.psiMap lambda p : M.Carrier) ∈
          closedToricPolydisc M upper (fun _ ↦ 0) S

/-- Bounded representatives in the two fixed affine `A₂` charts supply compact radial
fundamental domains. -/
public theorem radialSublevelCocompactness_of_twoChartRepresentatives
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (H : A2TwoChartRadialSublevelRepresentatives C) :
    RadialSublevelCocompactness C := by
  constructor
  intro a ha har
  obtain ⟨S, hS⟩ := H.bounded_representative a ha har
  let polydiscs : Set M.Carrier :=
    closedToricPolydisc M false (fun _ ↦ 0) S ∪
      closedToricPolydisc M true (fun _ ↦ 0) S
  let carrierCore : Set M.Carrier := {p | ‖M.t p‖ ≤ a} ∩ polydiscs
  let K : Set (LocalCarrier M r) := Subtype.val ⁻¹' carrierCore
  have hpolydiscs : IsCompact polydiscs :=
    (compact_closedToricPolydisc M false (fun _ ↦ 0) S).union
      (compact_closedToricPolydisc M true (fun _ ↦ 0) S)
  have hclosedRadius : IsClosed {p : M.Carrier | ‖M.t p‖ ≤ a} :=
    isClosed_le (continuous_norm.comp M.t_holomorphic.continuous) continuous_const
  have hcarrierCore : IsCompact carrierCore := hpolydiscs.inter_left hclosedRadius
  have hcarrierCore_local : carrierCore ⊆ cuspNeighborhood M r := by
    intro p hp
    exact (mem_cuspNeighborhood_iff M r p).2
      (mem_ball_zero_iff.mpr (hp.1.trans_lt har))
  have hK : IsCompact K := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hcarrierCore using 1
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p, hcarrierCore_local hp⟩, hp, rfl⟩
  refine ⟨K, hK, ?_, ?_⟩
  · intro p hp
    exact hp.1
  · intro p hp
    obtain ⟨lambda, upper, hlambda⟩ := hS p hp
    refine ⟨lambda, ?_⟩
    change (C.psiMap lambda p : M.Carrier) ∈ carrierCore
    refine ⟨?_, ?_⟩
    · change ‖M.t (C.psiMap lambda p)‖ ≤ a
      rw [C.psiMap_preserves_t]
      exact hp
    · cases upper
      · exact Or.inl hlambda
      · exact Or.inr hlambda

/-- A compact fundamental domain makes each closed radial sublevel of the quotient compact. -/
public theorem phaseCorrectedQuotientRadiusSublevel_isCompact
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (F : C.FixedPointEstimates) (H : RadialSublevelCocompactness C)
    (a : ℝ) (ha : 0 ≤ a) (har : a < r) :
    IsCompact {y : PhaseCorrectedToricQuotient C F |
      phaseCorrectedQuotientRadius C F y ≤ a} := by
  let _ := (C.toCuspActionData F).psiAction
  obtain ⟨K, hK, hKsub, hcover⟩ := H.compact_fundamental_domain a ha har
  let R : Setoid (LocalCarrier M r) :=
    MulAction.orbitRel (Multiplicative ParameterLattice) _
  have himage : IsCompact ((Quotient.mk R) '' K) := hK.image continuous_quot_mk
  convert himage using 1
  ext y
  induction y using Quotient.inductionOn with
  | _ p =>
    constructor
    · intro hp
      change ‖M.t p‖ ≤ a at hp
      obtain ⟨lambda, hlambda⟩ := hcover p hp
      refine ⟨C.psiMap lambda p, hlambda, ?_⟩
      apply Quotient.sound
      change MulAction.orbitRel (Multiplicative ParameterLattice) _
        (C.psiMap lambda p) p
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨Multiplicative.ofAdd lambda, ?_⟩
      change (C.toCuspActionData F).psiMap lambda p = C.psiMap lambda p
      exact (C.psiMap_eq_generic F lambda p).symm
    · rintro ⟨q, hq, hqp⟩
      change phaseCorrectedQuotientRadius C F (Quotient.mk _ p) ≤ a
      rw [← hqp, phaseCorrectedQuotientRadius_mk]
      exact hKsub hq

/-- The exact toric cocompactness input specialized to the actual normalized cusp
filling. -/
public def ActualCuspRadialSublevelCocompactness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : Prop :=
  RadialSublevelCocompactness
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius
        W.localWitness.radius_pos W.localWitness.radius_le)

/-- The concrete two-chart bounded-orbit statement for the actual `A₂` cusp action. -/
public def ActualA2TwoChartRadialSublevelRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : Prop :=
  A2TwoChartRadialSublevelRepresentatives
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius
        W.localWitness.radius_pos W.localWitness.radius_le)

/-- The cocompactness datum proves compactness of every nonnegative closed radial
sublevel in the actual cusp filling. -/
public theorem actualLocalCuspFillingRadiusSublevel_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (H : ActualCuspRadialSublevelCocompactness W)
    (a : ℝ) (ha : 0 ≤ a) (har : a < W.localWitness.radius) :
    IsCompact {y : actualLocalCuspFilling W |
      actualLocalCuspFillingRadius W y ≤ a} := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius
        W.localWitness.radius_pos W.localWitness.radius_le
  let F := W.localWitness.fixedPoint
  change IsCompact {y : PhaseCorrectedToricQuotient C F |
    phaseCorrectedQuotientRadius C F y ≤ a}
  exact phaseCorrectedQuotientRadiusSublevel_isCompact C F H a ha har

/-- The concrete two-chart bounded-orbit theorem implies compactness of actual cusp-filling
radial sublevels. -/
public theorem actualLocalCuspFillingRadiusSublevel_isCompact_of_twoChartRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (H : ActualA2TwoChartRadialSublevelRepresentatives W)
    (a : ℝ) (ha : 0 ≤ a) (har : a < W.localWitness.radius) :
    IsCompact {y : actualLocalCuspFilling W |
      actualLocalCuspFillingRadius W y ≤ a} := by
  apply actualLocalCuspFillingRadiusSublevel_isCompact W _ a ha har
  exact radialSublevelCocompactness_of_twoChartRepresentatives _ H

end

end SphereSixComplex.Geometry.CuspFillingRadialCompactness

namespace SphereSixComplex.Geometry.PaperAnalyticData

open Set CuspFilling CuspPuncturedCollarBridge
open CuspFillingRadialCompactness

noncomputable section

variable (P : PaperAnalyticData)

/-- The toric cocompactness statement discharges the exact cusp compact-core boundary
used by the four-piece compact cover. -/
public theorem actualLocalCuspRadialCoreCompactness_of_cocompactness
    (H : ActualCuspRadialSublevelCocompactness P.starCuspWitness) :
    P.ActualLocalCuspRadialCoreCompactness := by
  change ∀ a, a < P.starCuspWitness.localWitness.radius →
    IsCompact {y : actualLocalCuspFilling P.starCuspWitness |
      actualLocalCuspFillingRadius P.starCuspWitness y ≤ a}
  intro a ha
  by_cases ha0 : 0 ≤ a
  · exact actualLocalCuspFillingRadiusSublevel_isCompact
      P.starCuspWitness H a ha0 ha
  · have hempty : {y : actualLocalCuspFilling P.starCuspWitness |
        actualLocalCuspFillingRadius P.starCuspWitness y ≤ a} = ∅ := by
      ext y
      rw [mem_empty_iff_false, iff_false]
      intro hy
      have hnonneg : 0 ≤ actualLocalCuspFillingRadius P.starCuspWitness y := by
        induction y using Quotient.inductionOn with
        | _ p => exact norm_nonneg _
      exact (not_le_of_gt (lt_of_not_ge ha0)) (hnonneg.trans hy)
    rw [hempty]
    exact isCompact_empty

/-- The concrete `A₂` two-chart theorem discharges the cusp compact-core boundary. -/
public theorem actualLocalCuspRadialCoreCompactness_of_twoChartRepresentatives
    (H : ActualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness) :
    P.ActualLocalCuspRadialCoreCompactness := by
  apply P.actualLocalCuspRadialCoreCompactness_of_cocompactness
  exact radialSublevelCocompactness_of_twoChartRepresentatives _ H

end

end SphereSixComplex.Geometry.PaperAnalyticData
