/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricPolarModulus
public import SphereSixComplex.Geometry.QuotientTopology
public import SphereSixComplex.Topology.ActualCuspStraighteningRetraction
public import SphereSixComplex.Topology.NormalizedPolarHoneycombAmbientPhaseHomotopy
public import SphereSixComplex.Topology.NormalizedPolarHoneycombStabilizerMonotonicityProof

/-!
# Constructed reduction of normalized polar-honeycomb geometry

The explicit modulus on the constructed infinite `A₂` carrier supplies all polar, positive-deck,
and compact-phase fields.  This leaves only the topology of its positive quotient and central
honeycomb.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspFillingRadialCompactness
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningAlgebra
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspStraighteningHomeomorph
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The normalized positive deck formula preserves the explicit nonnegative part. -/
public theorem constructedPositiveDeck_mem
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ)
    (lambda : ParameterLattice) (q : constructedLocalPositivePart r) :
    normalizedPositiveDeckLocalMap N constructedModel r lambda
      (q : LocalCarrier constructedModel r) ∈ constructedLocalPositivePart r := by
  rw [mem_constructedLocalPositivePart_iff]
  exact carrierPositivePart_torusAction_fanShear
    (normalizedCuspPositiveTwist N lambda)
    (normalizedCuspPositiveTwist_real N lambda) lambda
    ((mem_constructedLocalPositivePart_iff r q).mp q.property)

public theorem constructedLocalPositivePart_t2Space (r : ℝ) :
    T2Space (constructedLocalPositivePart r) := by
  infer_instance

public theorem constructedLocalPositivePart_locallyCompactSpace (r : ℝ) :
    LocallyCompactSpace (constructedLocalPositivePart r) := by
  let _ : ChartedSpace ComplexModel constructedModel.Carrier := constructedModel.charts
  let _ : LocallyCompactSpace constructedModel.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel constructedModel.Carrier
  let _ : LocallyCompactSpace (LocalCarrier constructedModel r) :=
    (cuspNeighborhood constructedModel r).isOpen.locallyCompactSpace
  exact (constructedLocalPositivePart_isClosed r).locallyCompactSpace

/-- Every normalized positive deck transformation is continuous. -/
public theorem constructedPositiveDeck_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
    ContinuousConstSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart r) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
  constructor
  intro g
  rw [continuous_induced_rng, continuous_induced_rng]
  let lambda := Multiplicative.toAdd g
  change Continuous (fun q : constructedLocalPositivePart r ↦
    normalizedPositiveDeckCarrierMap N constructedModel lambda
      (((q : LocalCarrier constructedModel r) : constructedModel.Carrier)))
  exact (constructedModel.torusAction_holomorphic
      (normalizedCuspPositiveTwist N lambda)).continuous.comp
    ((constructedModel.fanShear_holomorphic lambda).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- At the quantitative cusp radius, straightening transfers proper discontinuity from the
actual action to its frozen action. -/
public theorem constructedFrozenAction_properlyDiscontinuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := frozenLocalCuspAction N constructedModel W.localWitness.radius
    ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (LocalCarrier constructedModel W.localWitness.radius) := by
  let _ := frozenLocalCuspAction N constructedModel W.localWitness.radius
  let C := CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N constructedModel W.localWitness.radius W.localWitness.radius_pos
      W.localWitness.radius_le
  let J := establishedContinuousTorusAction constructedModel
  let e := pointStraighteningHomeomorph J W
  constructor
  intro K L hK hL
  have hK' : IsCompact (e.symm '' K) := hK.image e.symm.continuous
  have hL' : IsCompact (e.symm '' L) := hL.image e.symm.continuous
  have hfinite := W.localWitness.compactOverlap (e.symm '' K) (e.symm '' L) hK' hL'
  have hpre := hfinite.preimage
    (Set.injOn_of_injective Multiplicative.toAdd.injective)
  apply hpre.subset
  rintro g ⟨x, ⟨k, hk, hkx⟩, hxL⟩
  change Multiplicative.toAdd g ∈
    {lambda : ParameterLattice |
      (C.psiMap lambda '' (e.symm '' K) ∩ e.symm '' L).Nonempty}
  refine ⟨e.symm x, ?_, Set.mem_image_of_mem e.symm hxL⟩
  refine ⟨e.symm k, Set.mem_image_of_mem e.symm hk, ?_⟩
  change C.psiMap (Multiplicative.toAdd g) (pointUnstraightening W k) =
    pointUnstraightening W x
  rw [actualPsiMap_pointUnstraightening W]
  exact congrArg (pointUnstraightening W) hkx

/-- The compact phase left after dividing the frozen complex multiplier by its positive radial
part. -/
public def frozenCompactPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) : CompactTorus :=
  fun i ↦ ⟨(phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂ) /
      (normalizedCuspPositiveTwist N lambda i : ℂ), by
    change ((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂ) /
      (normalizedCuspPositiveTwist N lambda i : ℂ)) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_div,
      norm_normalizedCuspPositiveTwist N lambda i]
    exact div_self (norm_ne_zero_iff.mpr (Units.ne_zero _))⟩

public theorem compactTorusEmbedding_frozenCompactPhase_mul
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) :
    compactTorusEmbedding (frozenCompactPhase N lambda) *
        normalizedCuspPositiveTwist N lambda =
      phaseEmbedding (N.phaseCoefficient lambda 0) := by
  ext i
  change ((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂ) /
      (normalizedCuspPositiveTwist N lambda i : ℂ)) *
      (normalizedCuspPositiveTwist N lambda i : ℂ) =
    (phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂ)
  exact div_mul_cancel₀ _ (Units.ne_zero _)

/-- A frozen deck map is its positive radial deck map followed by one compact phase. -/
public theorem frozenLocalPsiMap_eq_compactPhase_positiveDeck
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (lambda : ParameterLattice) (p : LocalCarrier M r) :
    frozenLocalPsiMap N M r lambda p =
      compactPhaseLocalAction M r (frozenCompactPhase N lambda)
        (normalizedPositiveDeckLocalMap N M r lambda p) := by
  apply Subtype.ext
  change M.torusAction (phaseEmbedding (N.phaseCoefficient lambda 0))
      (Additive.toMul (M.fanShear lambda) (p : M.Carrier)) =
    M.torusAction (compactTorusEmbedding (frozenCompactPhase N lambda))
      (M.torusAction (normalizedCuspPositiveTwist N lambda)
        (Additive.toMul (M.fanShear lambda) (p : M.Carrier)))
  rw [← compactTorusEmbedding_frozenCompactPhase_mul N lambda, map_mul,
    Equiv.Perm.mul_apply]

/-- Every ray component of the explicitly glued carrier is closed. -/
public theorem carrierCentralComponent_isClosed (v : ToricLattice) :
    IsClosed (carrierCentralComponent v) := by
  let _ := chartedSpace
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  have hsource : inclusion a z ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self z
  by_cases hv : v ∈ Set.range (a2Triangle a.1 a.2)
  · obtain ⟨i, rfl⟩ := hv
    let U := (toricChart a).source ∩
      toricChart a ⁻¹' {w : ComplexModel | w i ≠ 0}
    refine ⟨U, ?_, ?_, ?_⟩
    · intro q hq hcomponent
      exact hq.2 ((carrierCentralComponent_in_chart a i q hq.1).mp hcomponent)
    · exact (toricChart a).toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage
        (toricChart a).open_source
        (isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) i).continuous continuous_const)
    · refine ⟨hsource, ?_⟩
      intro hzero
      exact hp ((carrierCentralComponent_in_chart a i (inclusion a z) hsource).mpr hzero)
  · refine ⟨(toricChart a).source, ?_, (toricChart a).open_source, hsource⟩
    intro q hq hcomponent
    exact Set.disjoint_left.mp
      (otherCarrierCentralComponent_disjoint_chart a v hv) hcomponent hq

/-- The ray-component cover is locally finite: an affine chart meets only its three rays. -/
public theorem carrierCentralComponents_locallyFinite :
    LocallyFinite carrierCentralComponent := by
  let _ := chartedSpace
  intro p
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  have hsource : inclusion a z ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self z
  refine ⟨(toricChart a).source, (toricChart a).open_source.mem_nhds hsource, ?_⟩
  apply (Set.finite_range (a2Triangle a.1 a.2)).subset
  intro v hv
  by_contra hvrange
  obtain ⟨q, hcomponent, hqsource⟩ := hv
  exact Set.disjoint_left.mp
    (otherCarrierCentralComponent_disjoint_chart a v hvrange) hcomponent hqsource

/-- The explicit positive central fibre used as the honeycomb target. -/
public abbrev constructedPositiveCentralFiber (r : ℝ) :=
  {q : constructedLocalPositivePart r |
    constructedModel.t (q : LocalCarrier constructedModel r) = 0}

/-- The radius-independent global positive central fibre. -/
public abbrev constructedGlobalPositiveCentralFiber :=
  {x : carrierPositivePart | carrierHeight x = 0}

/-- For positive radius, the local positive central fibre is exactly the global positive central
fibre; the local height bound is automatic at height zero. -/
public def constructedPositiveCentralFiberHomeomorph (r : ℝ) (hr : 0 < r) :
    constructedPositiveCentralFiber r ≃ₜ constructedGlobalPositiveCentralFiber where
  toFun q :=
    ⟨⟨q.1.1.1, (mem_constructedLocalPositivePart_iff r q.1).mp q.1.property⟩,
      q.property⟩
  invFun x := by
    let p : LocalCarrier constructedModel r :=
      ⟨(show constructedModel.Carrier from x.1.1), by
      change carrierHeight x.1.1 ∈ Metric.ball 0 r
      rw [x.property]
      exact Metric.mem_ball_self hr⟩
    exact ⟨⟨p, (mem_constructedLocalPositivePart_iff r p).mpr x.1.property⟩,
      x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

/-- The positive cell cut out by one ray component of the central toric fibre. -/
public def constructedPositiveCentralCell (r : ℝ) (v : ToricLattice) :
    Set (constructedPositiveCentralFiber r) :=
  {q | (q.1.1.1 : Carrier) ∈ carrierCentralComponent v}

/-- Every positive central cell is closed. -/
public theorem constructedPositiveCentralCell_isClosed (r : ℝ) (v : ToricLattice) :
    IsClosed (constructedPositiveCentralCell r v) := by
  have hcentral : Continuous
      (fun q : constructedPositiveCentralFiber r ↦ q.1) :=
    continuous_subtype_val
  have hpositive : Continuous
      (fun q : constructedPositiveCentralFiber r ↦ q.1.1) :=
    continuous_subtype_val.comp hcentral
  have hlocal : Continuous
      (fun q : constructedPositiveCentralFiber r ↦ (q.1.1.1 : Carrier)) :=
    continuous_subtype_val.comp hpositive
  exact (carrierCentralComponent_isClosed v).preimage hlocal

/-- The positive central cells inherit local finiteness from the carrier components. -/
public theorem constructedPositiveCentralCells_locallyFinite (r : ℝ) :
    LocallyFinite (constructedPositiveCentralCell r) := by
  have hcentral : Continuous
      (fun q : constructedPositiveCentralFiber r ↦ q.1) :=
    continuous_subtype_val
  have hpositive : Continuous
      (fun q : constructedPositiveCentralFiber r ↦ q.1.1) :=
    continuous_subtype_val.comp hcentral
  have hf : Continuous
      (fun q : constructedPositiveCentralFiber r ↦ (q.1.1.1 : Carrier)) :=
    continuous_subtype_val.comp hpositive
  let f : constructedPositiveCentralFiber r → Carrier := fun q ↦ q.1.1.1
  intro q
  obtain ⟨U, hU, hfinite⟩ := carrierCentralComponents_locallyFinite (f q)
  refine ⟨f ⁻¹' U, hf.continuousAt hU, hfinite.subset ?_⟩
  intro v hv
  obtain ⟨x, hxcell, hxU⟩ := hv
  exact ⟨f x, hxcell, hxU⟩

/-- The ray cells cover the whole positive central fibre. -/
public theorem iUnion_constructedPositiveCentralCell (r : ℝ) :
    ⋃ v, constructedPositiveCentralCell r v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hzero : carrierHeight (q.1.1.1 : Carrier) = 0 := by
    exact q.property
  have hmem : (q.1.1.1 : Carrier) ∈ carrierHeight ⁻¹' {0} := hzero
  rw [carrierCentralFiber_eq_iUnion] at hmem
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmem
  exact Set.mem_iUnion.mpr ⟨v, hv⟩

/-- The six maximal cones in the star of a height-one ray. -/
public def chartAtCentralRay (v : ToricLattice) : Bool × Fin 3 → ChartIndex
  | (false, 0) => (false, v)
  | (false, 1) => (false, v - e₁)
  | (false, 2) => (false, v - e₂)
  | (true, 0) => (true, v - e₁)
  | (true, 1) => (true, v - e₂)
  | (true, 2) => (true, v - e₁ - e₂)

public theorem chart_eq_chartAtCentralRay_of_vertex
    (v : ToricLattice) (a : ChartIndex) (i : Fin 3)
    (h : a2Triangle a.1 a.2 i = v) :
    a = chartAtCentralRay v (a.1, i) := by
  rcases a with ⟨upper, w⟩
  cases upper <;> fin_cases i <;>
    simp [chartAtCentralRay, a2Triangle] at h ⊢
  all_goals rw [← h]
  all_goals simp [sub_eq_add_neg]
  all_goals abel

/-- Only six affine charts contain a prescribed central ray. -/
public theorem chartsContainingCentralRay_finite (v : ToricLattice) :
    {a : ChartIndex | v ∈ Set.range (a2Triangle a.1 a.2)}.Finite := by
  apply (Set.finite_range (chartAtCentralRay v)).subset
  intro a ha
  obtain ⟨i, hi⟩ := ha
  exact ⟨(a.1, i), (chart_eq_chartAtCentralRay_of_vertex v a i hi).symm⟩

/-- A closed unit affine toric polydisc is compact. -/
public theorem unitPolydisc_isCompact (a : ChartIndex) :
    IsCompact (unitPolydisc a) := by
  let _ := chartedSpace
  let K : Set RawCoordinates := {z | ∀ i, ‖z i‖ ≤ 1}
  have hK : IsCompact K := by
    have hprod : IsCompact
        {z : RawCoordinates | ∀ i, z i ∈ Metric.closedBall (0 : ℂ) 1} :=
      isCompact_pi_infinite fun _ ↦ isCompact_closedBall (0 : ℂ) 1
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hprod
  have heq : unitPolydisc a = inclusion a '' K := by
    ext p
    constructor
    · rintro ⟨hp, hbound⟩
      rw [toricChart_source] at hp
      obtain ⟨z, rfl⟩ := hp
      refine ⟨z, ?_, rfl⟩
      intro i
      rw [toricChart_inclusion] at hbound
      exact hbound i
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [toricChart_source]
        exact Set.mem_range_self z
      · intro i
        rw [toricChart_inclusion]
        exact hz i
  rw [heq]
  exact hK.image (inclusion_isOpenEmbedding a).continuous

/-- Each ray component is compact, being covered by the six compact affine polydiscs in its
star. -/
public theorem carrierCentralComponent_isCompact (v : ToricLattice) :
    IsCompact (carrierCentralComponent v) := by
  let _ := chartedSpace
  let S : Set ChartIndex := {a | v ∈ Set.range (a2Triangle a.1 a.2)}
  have hS : S.Finite := chartsContainingCentralRay_finite v
  have hcompact : IsCompact (⋃ a ∈ S, unitPolydisc a) :=
    hS.isCompact_biUnion fun a _ ↦ unitPolydisc_isCompact a
  apply hcompact.of_isClosed_subset (carrierCentralComponent_isClosed v)
  intro p hp
  have ht : carrierHeight p = 0 := by
    change p ∈ carrierHeight ⁻¹' {0}
    rw [carrierCentralFiber_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨v, hp⟩
  obtain ⟨a, ha⟩ := carrierCentralFiber_unitPolydisc_cover p ht
  have hchart : p ∈ (toricChart a).source := ha.1
  have hav : a ∈ S := by
    by_contra hnot
    exact Set.disjoint_left.mp
      (otherCarrierCentralComponent_disjoint_chart a v hnot) hp hchart
  exact Set.mem_iUnion₂.mpr ⟨a, hav, ha⟩

namespace LocallyFiniteClosedCover

/-- Projection from the disjoint union of a family of subsets. -/
public def projection {ι X : Type*} (A : ι → Set X) (p : Σ i, A i) : X :=
  p.2.1

public theorem projection_continuous {ι X : Type*} [TopologicalSpace X]
    (A : ι → Set X) : Continuous (projection A) :=
  continuous_sigma_iff.mpr fun _ ↦ continuous_subtype_val

public theorem projection_surjective {ι X : Type*} {A : ι → Set X}
    (hcover : ⋃ i, A i = Set.univ) : Function.Surjective (projection A) := by
  intro x
  have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨i, x, hi⟩, rfl⟩

/-- Projection from a locally finite closed cover is a closed map. -/
public theorem projection_isClosedMap {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hclosed : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) :
    IsClosedMap (projection A) := by
  intro S hS
  let F : ι → Set X := fun i ↦
    (Subtype.val : A i → X) '' ((fun x : A i ↦ Sigma.mk i x) ⁻¹' S)
  have hFclosed (i : ι) : IsClosed (F i) :=
    (hclosed i).isClosedMap_subtype_val _ (hS.preimage continuous_sigmaMk)
  have hFsub (i : ι) : F i ⊆ A i := by
    rintro x ⟨a, _, rfl⟩
    exact a.2
  have heq : projection A '' S = ⋃ i, F i := by
    ext x
    constructor
    · rintro ⟨⟨i, a⟩, ha, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩
    · intro hx
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i, a⟩, ha, rfl⟩
  rw [heq]
  exact (hloc.subset hFsub).isClosed_iUnion hFclosed

public theorem projection_isQuotientMap {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hcover : ⋃ i, A i = Set.univ)
    (hclosed : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) :
    Topology.IsQuotientMap (projection A) :=
  (projection_isClosedMap hclosed hloc).isQuotientMap (projection_continuous A)
    (projection_surjective hcover)

/-- Homeomorphisms on the members of an indexed cover assemble over the disjoint union. -/
public def sigmaHomeomorph {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y)
    (e : ∀ i, A i ≃ₜ B i) : (Σ i, A i) ≃ₜ (Σ i, B i) where
  toFun p := ⟨p.1, e p.1 p.2⟩
  invFun p := ⟨p.1, (e p.1).symm p.2⟩
  left_inv := by rintro ⟨i, a⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp
  continuous_toFun :=
    continuous_sigma_iff.mpr fun i ↦ continuous_sigmaMk.comp (e i).continuous
  continuous_invFun :=
    continuous_sigma_iff.mpr fun i ↦ continuous_sigmaMk.comp (e i).symm.continuous

public noncomputable def descend {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (x : X) : Y :=
  g (hf x).choose

public theorem descend_apply {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (hfg : ∀ a b, f a = f b → g a = g b) (a : A) :
    descend f g hf (f a) = g a :=
  hfg _ a (hf (f a)).choose_spec

public theorem descend_surjective {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (hfg : ∀ a b, f a = f b → g a = g b)
    (hg : Function.Surjective g) : Function.Surjective (descend f g hf) := by
  intro y
  obtain ⟨a, rfl⟩ := hg y
  exact ⟨f a, descend_apply f g hf hfg a⟩

public theorem descend_injective {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (hgf : ∀ a b, g a = g b → f a = f b) :
    Function.Injective (descend f g hf) := by
  intro x y h
  have he := hgf (hf x).choose (hf y).choose h
  exact (hf x).choose_spec.symm.trans (he.trans (hf y).choose_spec)

public theorem descend_continuous {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] (hq : Topology.IsQuotientMap f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b → g a = g b) : Continuous (descend f g hf) := by
  apply hq.continuous_iff.mpr
  have he : descend f g hf ∘ f = g := funext (descend_apply f g hf hfg)
  rwa [he]

/-- Compatible cellwise homeomorphisms on two locally finite closed covers glue to a global
homeomorphism. -/
public noncomputable def homeomorph {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y)
    (e : ∀ i, A i ≃ₜ B i) (hAcov : ⋃ i, A i = Set.univ)
    (hAcl : ∀ i, IsClosed (A i)) (hAloc : LocallyFinite A)
    (hBcov : ⋃ i, B i = Set.univ) (hBcl : ∀ i, IsClosed (B i))
    (hBloc : LocallyFinite B)
    (hglue : ∀ i j (x : A i) (y : A j),
      (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y)) : X ≃ₜ Y := by
  let f := projection A
  let g := projection B ∘ sigmaHomeomorph A B e
  have hf : Topology.IsQuotientMap f := projection_isQuotientMap hAcov hAcl hAloc
  have hg : Topology.IsQuotientMap g :=
    (projection_isQuotientMap hBcov hBcl hBloc).comp
      (sigmaHomeomorph A B e).isQuotientMap
  have hfg : ∀ a b, f a = f b ↔ g a = g b := fun a b ↦
    hglue a.1 b.1 a.2 b.2
  let E : X ≃ Y :=
    Equiv.ofBijective (descend f g hf.surjective)
      ⟨descend_injective f g hf.surjective (fun a b ↦ (hfg a b).mpr),
        descend_surjective f g hf.surjective (fun a b ↦ (hfg a b).mp) hg.surjective⟩
  refine
    { toEquiv := E
      continuous_toFun :=
        descend_continuous f g hf.surjective hf hg.continuous
          (fun a b ↦ (hfg a b).mp)
      continuous_invFun := ?_ }
  apply hg.continuous_iff.mpr
  change Continuous (E.symm ∘ g)
  have hcomp : E.symm ∘ g = f := by
    funext a
    apply E.injective
    change E (E.symm (g a)) = E (f a)
    rw [E.apply_symm_apply]
    exact (descend_apply f g hf.surjective (fun a b ↦ (hfg a b).mp) a).symm
  rw [hcomp]
  exact hf.continuous

end LocallyFiniteClosedCover

/-- Exact cellwise input still needed for the honeycomb homeomorphism.  All target-side
closed-cover facts are already supplied by the constructed carrier. -/
public structure ConstructedHoneycombCellData (r : ℝ) where
  planeCell : ToricLattice → Set (Fin 2 → ℝ)
  planeCell_cover : ⋃ v, planeCell v = Set.univ
  planeCell_closed : ∀ v, IsClosed (planeCell v)
  planeCell_locallyFinite : LocallyFinite planeCell
  cellHomeomorph : ∀ v, planeCell v ≃ₜ constructedPositiveCentralCell r v
  cellHomeomorph_compatible : ∀ v w (x : planeCell v) (y : planeCell w),
    (x : Fin 2 → ℝ) = (y : Fin 2 → ℝ) ↔
      (cellHomeomorph v x : constructedPositiveCentralFiber r) = cellHomeomorph w y

namespace ConstructedHoneycombCellData

/-- Compatible homeomorphisms on the planar and toric cells give the required honeycomb. -/
public noncomputable def honeycomb {r : ℝ} (H : ConstructedHoneycombCellData r) :
    (Fin 2 → ℝ) ≃ₜ constructedPositiveCentralFiber r :=
  LocallyFiniteClosedCover.homeomorph H.planeCell (constructedPositiveCentralCell r)
    H.cellHomeomorph H.planeCell_cover H.planeCell_closed H.planeCell_locallyFinite
    (iUnion_constructedPositiveCentralCell r) (constructedPositiveCentralCell_isClosed r)
    (constructedPositiveCentralCells_locallyFinite r) H.cellHomeomorph_compatible

end ConstructedHoneycombCellData

/-- The logarithmic norm of the positive frozen multiplier is the frozen correction matrix. -/
public theorem log_norm_normalizedCuspPositiveTwist
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice)
    (i : Fin 2) :
    Real.log ‖((normalizedCuspPositiveTwist N lambda i.castSucc : ℂˣ) : ℂ)‖ =
      (phaseLogMatrix N 0).mulVec (realParameter lambda) i := by
  rw [norm_normalizedCuspPositiveTwist]
  fin_cases i
  · simpa [phaseEmbedding_apply_zero] using
      log_norm_phaseCoefficient N lambda 0 0
  · simpa [phaseEmbedding_apply_one] using
      log_norm_phaseCoefficient N lambda 0 1

/-- A fixed point of the positive deck action away from the central fibre satisfies the frozen
logarithmic displacement equation. -/
public theorem normalizedPositiveDeck_offCentral_logarithmic_equation
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) {r : ℝ}
    (lambda : ParameterLattice) (p : LocalCarrier M r) (ht : M.t p ≠ 0)
    (hfixed : normalizedPositiveDeckLocalMap N M r lambda p = p)
    (i : Fin 2) :
    (phaseLogMatrix N 0).mulVec (realParameter lambda) i +
      Real.log ‖M.t p‖ * (shearVector lambda i : ℝ) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, M.torusEmbedding x = (p : M.Carrier) := by
    have hp : (p : M.Carrier) ∈ {q | M.t q ≠ 0} := ht
    rw [← M.torus_range] at hp
    exact hp
  have hfixed' := congrArg Subtype.val hfixed
  change normalizedPositiveDeckCarrierMap N M lambda (p : M.Carrier) = p at hfixed'
  rw [normalizedPositiveDeckCarrierMap, ← hx, M.fanShear_torus,
    M.torusAction_torus] at hfixed'
  have htorus : normalizedCuspPositiveTwist N lambda * denseTorusShear lambda x = x :=
    M.torus_openEmbedding.injective hfixed'
  have hi := congrFun htorus i.castSucc
  have hi' : normalizedCuspPositiveTwist N lambda i.castSucc *
      x 2 ^ shearVector lambda i = 1 := by
    fin_cases i
    · change normalizedCuspPositiveTwist N lambda 0 *
        (x 0 * x 2 ^ shearVector lambda 0) = x 0 at hi
      change normalizedCuspPositiveTwist N lambda 0 *
        x 2 ^ shearVector lambda 0 = 1
      apply mul_right_cancel (b := x 0)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hi
    · change normalizedCuspPositiveTwist N lambda 1 *
        (x 1 * x 2 ^ shearVector lambda 1) = x 1 at hi
      change normalizedCuspPositiveTwist N lambda 1 *
        x 2 ^ shearVector lambda 1 = 1
      apply mul_right_cancel (b := x 1)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hi
  have hnorm := congrArg (fun u : ℂˣ ↦ ‖(u : ℂ)‖) hi'
  simp only [Units.val_mul, norm_mul, Units.val_one, norm_one] at hnorm
  rw [show ((↑(x 2 ^ shearVector lambda i) : ℂ)) =
      (x 2 : ℂ) ^ shearVector lambda i by
        exact map_zpow (Units.coeHom ℂ) (x 2) (shearVector lambda i),
    norm_zpow] at hnorm
  have hlog := congrArg Real.log hnorm
  rw [Real.log_mul (ne_of_gt (Units.norm_pos _))
      (zpow_ne_zero _ (ne_of_gt (Units.norm_pos _))),
    Real.log_zpow, Real.log_one] at hlog
  rw [log_norm_normalizedCuspPositiveTwist] at hlog
  have htpx : M.t p = (x 2 : ℂ) := by
    rw [← hx, M.t_torus]
  rw [htpx]
  linarith

/-- A fixed point of the positive deck action on the central fibre has zero lattice parameter. -/
public theorem normalizedPositiveDeck_central_fixedPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) {r : ℝ}
    (lambda : ParameterLattice) (p : LocalCarrier M r) (ht : M.t p = 0)
    (hfixed : normalizedPositiveDeckLocalMap N M r lambda p = p) :
    lambda = 0 := by
  have hsupport : (componentSupport M (p : M.Carrier)).Nonempty :=
    componentSupport_nonempty_of_t_eq_zero M ht
  have hforward : ∀ v ∈ componentSupport M (p : M.Carrier),
      v + shearVector lambda ∈ componentSupport M (p : M.Carrier) := by
    intro v hv
    have hshear : Additive.toMul (M.fanShear lambda) (p : M.Carrier) ∈
        M.centralComponent (v + shearVector lambda) := by
      rw [← M.fanShear_component lambda v]
      exact ⟨p, hv, rfl⟩
    have hphase := (M.torusAction_centralComponent
      (normalizedCuspPositiveTwist N lambda)
      (v + shearVector lambda)
      (Additive.toMul (M.fanShear lambda) (p : M.Carrier))).mpr hshear
    have hfixed' := congrArg Subtype.val hfixed
    change normalizedPositiveDeckCarrierMap N M lambda (p : M.Carrier) = p at hfixed'
    rw [normalizedPositiveDeckCarrierMap] at hfixed'
    rw [hfixed'] at hphase
    exact hphase
  have hshear_zero : shearVector lambda = 0 :=
    translation_eq_zero_of_finite_forward_invariant
      (componentSupport_finite M p) hsupport hforward
  apply shearVector_injective
  simpa [shearVector] using hshear_zero

/-- Frozen displacement injectivity rules out positive-deck fixed points off the central fibre. -/
public theorem normalizedPositiveDeck_offCentral_fixedPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (lambda : ParameterLattice)
    (p : LocalCarrier constructedModel W.localWitness.radius)
    (ht : constructedModel.t p ≠ 0)
    (hfixed : normalizedPositiveDeckLocalMap N constructedModel
      W.localWitness.radius lambda p = p) :
    lambda = 0 := by
  let d : Fin 2 → ℝ := fun i ↦ (shearVector lambda i : ℝ)
  have hlog_ne : Real.log ‖constructedModel.t p‖ ≠ 0 := by
    have hnorm_pos : 0 < ‖constructedModel.t p‖ := norm_pos_iff.mpr ht
    have hnorm_lt : ‖constructedModel.t p‖ < 1 :=
      (mem_ball_zero_iff.mp p.property).trans W.localWitness.radius_lt_one
    exact Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt)
  have hzero : frozenEffectiveFanDisplacement N (constructedModel.t p) d = 0 := by
    funext i
    have hi := normalizedPositiveDeck_offCentral_logarithmic_equation
      N constructedModel lambda p ht hfixed i
    have hinv : realFanShearInverse d = realParameter lambda := by
      change realFanShearInverse (fun i ↦ (shearVector lambda i : ℝ)) =
        realParameter lambda
      exact realFanShearInverse_shearVector lambda
    simp only [frozenEffectiveFanDisplacement, Pi.add_apply, hinv, Pi.zero_apply]
    dsimp only [d]
    field_simp [hlog_ne]
    linarith
  have hmulzero :
      (frozenDisplacementMatrix N (constructedModel.t p)).mulVec d = 0 := by
    rw [frozenDisplacementMatrix_mulVec]
    exact hzero
  have hmatrix_unit : IsUnit (frozenDisplacementMatrix N (constructedModel.t p)) :=
    (frozenDisplacementMatrix N (constructedModel.t p)).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr
        (frozenDisplacementMatrix_det_ne_zero W ⟨p, ht⟩))
  have hinjective : Function.Injective
      (frozenDisplacementMatrix N (constructedModel.t p)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hmatrix_unit
  have hdzero : d = 0 := by
    apply hinjective
    rw [hmulzero, Matrix.mulVec_zero]
  have hshear_zero : shearVector lambda = 0 := by
    funext i
    have hi := congrFun hdzero i
    dsimp only [d] at hi
    change (shearVector lambda i : ℝ) = (0 : ℝ) at hi
    exact_mod_cast hi
  apply shearVector_injective
  simpa [shearVector] using hshear_zero

/-- The positive deck action has no nontrivial fixed parameter at the quantitative radius. -/
public theorem normalizedPositiveDeck_fixedPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (lambda : ParameterLattice)
    (p : LocalCarrier constructedModel W.localWitness.radius)
    (hfixed : normalizedPositiveDeckLocalMap N constructedModel
      W.localWitness.radius lambda p = p) :
    lambda = 0 := by
  by_cases ht : constructedModel.t p = 0
  · exact normalizedPositiveDeck_central_fixedPoint N constructedModel
      lambda p ht hfixed
  · exact normalizedPositiveDeck_offCentral_fixedPoint W lambda p ht hfixed

/-- The normalized positive deck action is free at the quantitative cusp radius. -/
public theorem constructedPositiveDeck_isCancelSMul
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    IsCancelSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart W.localWitness.radius) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hfixed
  have hlocal : normalizedPositiveDeckLocalMap N constructedModel
      W.localWitness.radius (Multiplicative.toAdd g)
      (q : LocalCarrier constructedModel W.localWitness.radius) = q :=
    congrArg Subtype.val hfixed
  have hlambda : Multiplicative.toAdd g = 0 :=
    normalizedPositiveDeck_fixedPoint W (Multiplicative.toAdd g) q hlocal
  exact Multiplicative.toAdd.injective (by simpa using hlambda)

/-- Proper discontinuity descends from the frozen action to its positive radial section. -/
public theorem constructedPositiveDeck_properlyDiscontinuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart W.localWitness.radius) := by
  let r := W.localWitness.radius
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
  let _ := frozenLocalCuspAction N constructedModel r
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (LocalCarrier constructedModel r) :=
    constructedFrozenAction_properlyDiscontinuous W
  constructor
  intro K L hK hL
  let K₀ : Set (LocalCarrier constructedModel r) :=
    Subtype.val '' K
  let L₀ : Set (LocalCarrier constructedModel r) :=
    compactPhaseOrbit constructedModel r (constructedLocalPositivePart r) ''
      (Set.univ ×ˢ L)
  have hK₀ : IsCompact K₀ := hK.image continuous_subtype_val
  have hL₀ : IsCompact L₀ :=
    (isCompact_univ.prod hL).image
      (continuous_compactPhaseOrbit constructedModel r (constructedLocalPositivePart r))
  have hfinite : Set.Finite {g : Multiplicative ParameterLattice |
      (((g • ·) '' K₀) ∩ L₀).Nonempty} :=
    finite_disjoint_inter_image hK₀ hL₀
  apply hfinite.subset
  rintro g ⟨y, ⟨q, hqK, hqy⟩, hyL⟩
  let lambda := Multiplicative.toAdd g
  have hpositive :
      normalizedPositiveDeckLocalMap N constructedModel r lambda
          (q : LocalCarrier constructedModel r) =
        (y : LocalCarrier constructedModel r) := by
    exact congrArg Subtype.val hqy
  let x := frozenLocalPsiMap N constructedModel r lambda
    (q : LocalCarrier constructedModel r)
  refine ⟨x, ?_, ?_⟩
  · refine ⟨(q : LocalCarrier constructedModel r), ⟨q, hqK, rfl⟩, ?_⟩
    rfl
  · refine ⟨(frozenCompactPhase N lambda, y), ⟨Set.mem_univ _, hyL⟩, ?_⟩
    change compactPhaseLocalAction constructedModel r
      (frozenCompactPhase N lambda) (y : LocalCarrier constructedModel r) = x
    rw [show x = frozenLocalPsiMap N constructedModel r lambda
        (q : LocalCarrier constructedModel r) by rfl,
      frozenLocalPsiMap_eq_compactPhase_positiveDeck, hpositive]

/-- Proper discontinuity and freeness discharge the covering field through Mathlib's regular
orbit-cover theorem. -/
public theorem constructedQuotientCovering_of_properlyDiscontinuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ)
    (hcancel :
      letI := normalizedPositiveDeckAction N constructedModel
        (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
      IsCancelSMul (Multiplicative ParameterLattice) (constructedLocalPositivePart r))
    (hproper :
      letI := normalizedPositiveDeckAction N constructedModel
        (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
      ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
        (constructedLocalPositivePart r)) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection (constructedLocalPositivePart r))
      (Multiplicative ParameterLattice) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart r) := constructedPositiveDeck_continuous N r
  let _ : T2Space (constructedLocalPositivePart r) :=
    constructedLocalPositivePart_t2Space r
  let _ : LocallyCompactSpace (constructedLocalPositivePart r) :=
    constructedLocalPositivePart_locallyCompactSpace r
  let _ : IsCancelSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart r) := hcancel
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart r) := hproper
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The positive orbit projection at the quantitative cusp radius is a covering quotient. -/
public theorem constructedPositiveDeck_quotientCovering
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection
        (constructedLocalPositivePart W.localWitness.radius))
      (Multiplicative ParameterLattice) :=
  constructedQuotientCovering_of_properlyDiscontinuous N W.localWitness.radius
    (constructedPositiveDeck_isCancelSMul W)
    (constructedPositiveDeck_properlyDiscontinuous W)

/-- Proper discontinuity also discharges the Hausdorff quotient field. -/
public theorem constructedQuotient_t2_of_properlyDiscontinuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ)
    (hproper :
      letI := normalizedPositiveDeckAction N constructedModel
        (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
      ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
        (constructedLocalPositivePart r)) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
    T2Space (PolarHoneycombData.OrbitQuotient (constructedLocalPositivePart r)) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart r) := constructedPositiveDeck_continuous N r
  let _ : T2Space (constructedLocalPositivePart r) :=
    constructedLocalPositivePart_t2Space r
  let _ : LocallyCompactSpace (constructedLocalPositivePart r) :=
    constructedLocalPositivePart_locallyCompactSpace r
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart r) := hproper
  exact SphereSixComplex.Geometry.orbitQuotient_t2Space

/-- The positive quotient at the quantitative cusp radius is Hausdorff. -/
public theorem constructedPositiveDeck_quotient_t2
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    T2Space (PolarHoneycombData.OrbitQuotient
      (constructedLocalPositivePart W.localWitness.radius)) :=
  constructedQuotient_t2_of_properlyDiscontinuous N W.localWitness.radius
    (constructedPositiveDeck_properlyDiscontinuous W)

/-- The explicit constructed modulus is invariant under every compact phase. -/
public theorem constructedLocalModulus_compactPhase (r : ℝ) (k : CompactTorus)
    (p : constructedLocalPositivePart r) :
    constructedLocalModulusRetraction r
        (compactPhaseOrbit constructedModel r (constructedLocalPositivePart r) (k, p)) =
      constructedLocalModulusRetraction r p := by
  apply Subtype.ext
  apply Subtype.ext
  exact carrierModulus_compactTorusAction k
    (show Carrier from (p : LocalCarrier constructedModel r).1)

/-- The remaining topological residue after the explicit carrier construction. -/
public structure ConstructedPolarHoneycombTopologicalData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ) where
  honeycomb : (Fin 2 → ℝ) ≃ₜ
    {q : constructedLocalPositivePart r |
      constructedModel.t (q : LocalCarrier constructedModel r) = 0}
  quotientCovering :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection (constructedLocalPositivePart r))
      (Multiplicative ParameterLattice)
  positive_contractible : ContractibleSpace (constructedLocalPositivePart r)
  quotient_relativeCW :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
    Topology.RelCWComplex
      (Set.univ : Set (PolarHoneycombData.OrbitQuotient
        (constructedLocalPositivePart r)))
      (PolarHoneycombData.orbitCore
        {q : constructedLocalPositivePart r |
          constructedModel.t (q : LocalCarrier constructedModel r) = 0})
  quotient_t2 :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart r) (constructedPositiveDeck_mem N r)
    T2Space (PolarHoneycombData.OrbitQuotient (constructedLocalPositivePart r))

/-- At the quantitative cusp radius, only the honeycomb, its ambient contractibility, and the
relative CW structure remain: covering and Hausdorffness are consequences of the explicit
positive deck action. -/
public structure ConstructedPolarHoneycombResidualData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) where
  honeycomb : (Fin 2 → ℝ) ≃ₜ
    {q : constructedLocalPositivePart W.localWitness.radius |
      constructedModel.t
        (q : LocalCarrier constructedModel W.localWitness.radius) = 0}
  positive_contractible :
    ContractibleSpace (constructedLocalPositivePart W.localWitness.radius)
  quotient_relativeCW :
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    Topology.RelCWComplex
      (Set.univ : Set (PolarHoneycombData.OrbitQuotient
        (constructedLocalPositivePart W.localWitness.radius)))
      (PolarHoneycombData.orbitCore
        {q : constructedLocalPositivePart W.localWitness.radius |
          constructedModel.t
            (q : LocalCarrier constructedModel W.localWitness.radius) = 0})

namespace ConstructedPolarHoneycombResidualData

/-- Add the proved positive-deck covering and Hausdorff fields. -/
public def toTopologicalData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (T : ConstructedPolarHoneycombResidualData W) :
    ConstructedPolarHoneycombTopologicalData N W.localWitness.radius where
  honeycomb := T.honeycomb
  quotientCovering := constructedPositiveDeck_quotientCovering W
  positive_contractible := T.positive_contractible
  quotient_relativeCW := T.quotient_relativeCW
  quotient_t2 := constructedPositiveDeck_quotient_t2 W

end ConstructedPolarHoneycombResidualData

namespace ConstructedPolarHoneycombTopologicalData

/-- Add the proved polar and deck fields to the remaining topological residue. -/
public def toConstructionData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {r : ℝ}
    (T : ConstructedPolarHoneycombTopologicalData N r) :
    NormalizedPolarHoneycombConstructionData N constructedModel r where
  positivePart := constructedLocalPositivePart r
  modulus := constructedLocalModulusRetraction r
  modulus_fixed := constructedLocalModulusRetraction_fixed r
  modulus_t := constructedLocalModulusRetraction_t r
  polar_surjective := constructedLocalModulusRetraction_polar_surjective r
  honeycomb := T.honeycomb
  positiveDeck_mem := constructedPositiveDeck_mem N r
  quotientCovering := T.quotientCovering
  positive_contractible := T.positive_contractible
  quotient_relativeCW := T.quotient_relativeCW
  quotient_t2 := T.quotient_t2

/-- Its modulus has the compact-phase invariance needed by the phase-spreading reduction. -/
public theorem toConstructionData_invariantModulus
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {r : ℝ}
    (T : ConstructedPolarHoneycombTopologicalData N r) :
    CompactPhaseInvariantModulus T.toConstructionData := by
  exact constructedLocalModulus_compactPhase r

/-- The reduced topological residue implies the full normalized phase geometry. -/
public def toPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {r : ℝ}
    (T : ConstructedPolarHoneycombTopologicalData N r) :
    {Q : NormalizedPolarHoneycombConstructionData N constructedModel r //
      PolarPhaseGeometricCore constructedModel r Q.toPolarHoneycombData} :=
  ⟨T.toConstructionData,
    polarPhaseGeometricCore_of_invariantModulus_only T.toConstructionData
      T.toConstructionData_invariantModulus⟩

end ConstructedPolarHoneycombTopologicalData

namespace ConstructedPolarHoneycombResidualData

/-- The three-field geometric residue implies the full normalized phase geometry. -/
public def toPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (T : ConstructedPolarHoneycombResidualData W) :
    {Q : NormalizedPolarHoneycombConstructionData N constructedModel
        W.localWitness.radius //
      PolarPhaseGeometricCore constructedModel W.localWitness.radius
        Q.toPolarHoneycombData} :=
  T.toTopologicalData.toPhaseGeometry

end ConstructedPolarHoneycombResidualData

/-- The three remaining topological fields suffice at the actual quantitative cusp radius. -/
public theorem normalizedPolarHoneycombPhaseGeometry_of_constructedResidual
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (h : Nonempty (ConstructedPolarHoneycombResidualData W)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N constructedModel
        W.localWitness.radius //
      PolarPhaseGeometricCore constructedModel W.localWitness.radius
        Q.toPolarHoneycombData} :=
  h.map ConstructedPolarHoneycombResidualData.toPhaseGeometry

/-- A construction of the five remaining topological fields replaces the broad phase axiom for
the explicit model. -/
public theorem normalizedPolarHoneycombPhaseGeometry_of_constructedTopology
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (r : ℝ)
    (h : Nonempty (ConstructedPolarHoneycombTopologicalData N r)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N constructedModel r //
      PolarPhaseGeometricCore constructedModel r Q.toPolarHoneycombData} :=
  h.map ConstructedPolarHoneycombTopologicalData.toPhaseGeometry

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
