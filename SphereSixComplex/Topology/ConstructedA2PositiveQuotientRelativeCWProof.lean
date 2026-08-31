module

public import SphereSixComplex.Topology.ConstructedA2PolarHoneycombCoordinateProof
public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Relative CW attachments for the constructed positive quotient

The free and properly discontinuous positive deck action makes the orbit projection a covering
and its quotient Hausdorff, but these facts alone do not construct characteristic maps for a CW
structure.  This file proves that the central orbit core is closed and packages the remaining
geometric input as locally finite relative-cell attachments.  Local finiteness supplies the weak
topology axiom, so the attachment data assemble directly into the required relative CW complex.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The orbit quotient of the constructed positive part at the quantitative cusp radius. -/
public abbrev ConstructedA2PositiveQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  PolarHoneycombData.OrbitQuotient
    (constructedLocalPositivePart W.localWitness.radius)

/-- The image of the zero-height honeycomb in the constructed positive quotient. -/
public abbrev ConstructedA2PositiveQuotientCore
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ConstructedA2PositiveQuotient W) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  PolarHoneycombData.orbitCore
    {q : constructedLocalPositivePart W.localWitness.radius |
      constructedModel.t
        (q : LocalCarrier constructedModel W.localWitness.radius) = 0}

/-- The zero-height fibre is closed in the constructed positive part. -/
public theorem constructedPositiveCentralFiber_isClosed (r : ℝ) :
    IsClosed {q : constructedLocalPositivePart r |
      constructedModel.t (q : LocalCarrier constructedModel r) = 0} := by
  exact isClosed_singleton.preimage
    (constructedModel.t_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The zero-height fibre is saturated under the normalized positive deck action. -/
public theorem constructedPositiveDeck_central_preimage
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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
            (q : LocalCarrier constructedModel W.localWitness.radius) = 0} =
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : LocalCarrier constructedModel W.localWitness.radius) = 0} := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  let central := {q : constructedLocalPositivePart W.localWitness.radius |
    constructedModel.t (q : LocalCarrier constructedModel W.localWitness.radius) = 0}
  have hmem (lambda : ParameterLattice)
      (q : constructedLocalPositivePart W.localWitness.radius) :
      (Multiplicative.ofAdd lambda) • q ∈ central ↔ q ∈ central := by
    change constructedModel.t
        (((Multiplicative.ofAdd lambda) • q :
          constructedLocalPositivePart W.localWitness.radius) :
          LocalCarrier constructedModel W.localWitness.radius) = 0 ↔
      constructedModel.t
        (q : LocalCarrier constructedModel W.localWitness.radius) = 0
    change constructedModel.t
        (normalizedPositiveDeckLocalMap N constructedModel W.localWitness.radius lambda
          (q : LocalCarrier constructedModel W.localWitness.radius)) = 0 ↔ _
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
public theorem constructedPositiveDeck_orbitCore_isClosed
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsClosed (ConstructedA2PositiveQuotientCore W) := by
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
          (q : LocalCarrier constructedModel W.localWitness.radius) = 0})
  rw [constructedPositiveDeck_central_preimage W]
  exact constructedPositiveCentralFiber_isClosed W.localWitness.radius

/-- The exact locally finite attachment data still needed for the positive quotient.  The core
closedness and the weak-topology condition are consequences rather than fields. -/
public structure ConstructedA2PositiveQuotientCWAttachmentData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) where
  cell : ℕ → Type
  map : (n : ℕ) → cell n → PartialEquiv (Fin n → ℝ) (ConstructedA2PositiveQuotient W)
  source_eq : ∀ n i, (map n i).source = ball 0 1
  continuousOn : ∀ n i, ContinuousOn (map n i) (closedBall 0 1)
  continuousOn_symm : ∀ n i, ContinuousOn (map n i).symm (map n i).target
  pairwiseDisjoint :
    (Set.univ : Set (Σ n, cell n)).PairwiseDisjoint
      (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  disjointCore : ∀ n i,
    Disjoint (map n i '' ball 0 1) (ConstructedA2PositiveQuotientCore W)
  frontier_finite : ∀ n i, ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1)
      (ConstructedA2PositiveQuotientCore W ∪
        ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  closedCells_locallyFinite :
    LocallyFinite (fun ni : Σ n, cell n ↦ map ni.1 ni.2 '' closedBall 0 1)
  union :
    ConstructedA2PositiveQuotientCore W ∪
      ⋃ ni : Σ n, cell n, map ni.1 ni.2 '' closedBall 0 1 = Set.univ

namespace ConstructedA2PositiveQuotientCWAttachmentData

/-- Locally finite attachment data assemble into the required relative CW structure. -/
@[instance_reducible]
public noncomputable def toRelativeCW
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (A : ConstructedA2PositiveQuotientCWAttachmentData W) :
    ConstructedA2PositiveQuotientRelativeCW W where
  cell := A.cell
  map := A.map
  source_eq := A.source_eq
  continuousOn := A.continuousOn
  continuousOn_symm := A.continuousOn_symm
  pairwiseDisjoint' := A.pairwiseDisjoint
  disjointBase' := A.disjointCore
  mapsTo := A.frontier_finite
  closed' S _ hS := by
    have hlf : LocallyFinite
        (fun ni : Σ n, A.cell n ↦
          S ∩ A.map ni.1 ni.2 '' closedBall 0 1) :=
      A.closedCells_locallyFinite.subset fun _ ↦ inter_subset_right
    have hclosedCells : IsClosed
        (⋃ ni : Σ n, A.cell n, S ∩ A.map ni.1 ni.2 '' closedBall 0 1) :=
      hlf.isClosed_iUnion fun ni ↦ hS.1 ni.1 ni.2
    rw [← inter_univ S, ← A.union, inter_union_distrib_left, inter_iUnion]
    exact hS.2.union hclosedCells
  isClosedBase := constructedPositiveDeck_orbitCore_isClosed W
  union' := by
    simpa only [iUnion_sigma] using A.union

end ConstructedA2PositiveQuotientCWAttachmentData

/-- Existence of explicit locally finite attachments gives component three of the constructed
polar-honeycomb coordinate package. -/
public theorem constructedA2PositiveQuotientRelativeCW_of_attachments
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (h : Nonempty (ConstructedA2PositiveQuotientCWAttachmentData W)) :
    Nonempty (ConstructedA2PositiveQuotientRelativeCW W) :=
  h.map ConstructedA2PositiveQuotientCWAttachmentData.toRelativeCW

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
