module

public import SphereSixComplex.Geometry.CuspToricLoopVanishing
public import SphereSixComplex.Topology.OpenCoverFundamentalGroup

/-!
# Fundamental-group surjectivity for the cusp collar

The local toric cusp is covered by its affine fan charts.  Every chart cut out by the cusp
radius is a contractible base-cone region, while all charts contain the same connected dense
torus locus.  The open-cover generation theorem therefore makes the local carrier's fundamental
group trivial at a torus basepoint.  This is the geometric input needed to transfer surjectivity
through the phase-corrected lattice quotient.
-/

@[expose] public section

noncomputable section

open Topology Set
open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open CuspCombinatorics
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricModel.Model
open CuspLocalPhaseAction CuspFilling CuspPeriodExpansion
open SphereSixComplex.Topology

/-- The additive cusp cover maps onto the raw punctured local toric carrier. -/
@[expose] public noncomputable def additiveCuspRadiusToPuncturedLocalCarrier
    (M : Model) (r : ℝ) :
    additiveCuspRadiusCover r → {p : LocalCarrier M r // M.t p ≠ 0} :=
  fun a ↦ additiveToPuncturedLocalHomeomorph M r (Quotient.mk _ a)

public theorem additiveCuspRadiusToPuncturedLocalCarrier_continuous
    (M : Model) (r : ℝ) :
    Continuous (additiveCuspRadiusToPuncturedLocalCarrier M r) :=
  (additiveToPuncturedLocalHomeomorph M r).continuous.comp continuous_quot_mk

public theorem additiveCuspRadiusToPuncturedLocalCarrier_surjective
    (M : Model) (r : ℝ) :
    Function.Surjective (additiveCuspRadiusToPuncturedLocalCarrier M r) := by
  intro p
  obtain ⟨q, rfl⟩ := (additiveToPuncturedLocalHomeomorph M r).surjective p
  induction q using Quotient.inductionOn with
  | _ a => exact ⟨a, rfl⟩

/-- The raw punctured local cusp carrier is path connected. -/
public theorem puncturedLocalCarrier_pathConnected
    (M : Model) {r : ℝ} (hr : 0 < r) :
    PathConnectedSpace {p : LocalCarrier M r // M.t p ≠ 0} := by
  let _ : PathConnectedSpace (additiveCuspRadiusCover r) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((additiveCuspRadiusCover_convex r).isPathConnected
        ⟨additiveCuspRadiusPoint hr, (additiveCuspRadiusPoint hr).property⟩)
  exact (additiveCuspRadiusToPuncturedLocalCarrier_surjective M r).pathConnectedSpace
    (additiveCuspRadiusToPuncturedLocalCarrier_continuous M r)

/-- The connected dense punctured locus forces the full local carrier to be connected. -/
public theorem localCarrier_connected (M : Model) {r : ℝ} (hr : 0 < r) :
    ConnectedSpace (LocalCarrier M r) := by
  let D : Set (LocalCarrier M r) := {p | M.t p ≠ 0}
  let _ : PathConnectedSpace D := puncturedLocalCarrier_pathConnected M hr
  have hD : IsConnected D := isConnected_iff_connectedSpace.mpr inferInstance
  have hdense : Dense D := puncturedLocalCarrier_dense M r
  exact connectedSpace_iff_univ.mpr
    (hD.subset_closure (Set.subset_univ D) (by
      rw [hdense.closure_eq]))

/-- The local carrier is path connected because it is an open complex submanifold and connected. -/
public theorem localCarrier_pathConnected (M : Model) {r : ℝ} (hr : 0 < r) :
    PathConnectedSpace (LocalCarrier M r) := by
  let _ := M.topology
  let _ := M.charts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ M.Carrier := M.manifold
  let _ : ChartedSpace ComplexModel (LocalCarrier M r) :=
    (cuspNeighborhood M r).instChartedSpace
  let _ : ConnectedSpace (LocalCarrier M r) := localCarrier_connected M hr
  let _ : LocallyPathConnectedSpace (LocalCarrier M r) :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel (LocalCarrier M r)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- The part of the local cusp carrier lying in one affine toric chart. -/
public def localCarrierToricChartSet (M : Model) (r : ℝ)
    (i : Bool × ToricLattice) : Set (LocalCarrier M r) :=
  {p | p.1 ∈ (M.toricChart i.1 i.2).source}

public theorem localCarrierToricChartSet_isOpen (M : Model) (r : ℝ)
    (i : Bool × ToricLattice) :
    IsOpen (localCarrierToricChartSet M r i) :=
  (M.toricChart i.1 i.2).open_source.preimage continuous_subtype_val

/-- A radius-cut affine toric chart is exactly the star-convex base-cone cusp region. -/
@[expose] public noncomputable def localCarrierToricChartHomeomorph
    (M : Model) (r : ℝ) (i : Bool × ToricLattice) :
    localCarrierToricChartSet M r i ≃ₜ baseConeCuspRegion r where
  toFun p := ⟨M.toricChart i.1 i.2 p.1.1, by
    change ‖(M.toricChart i.1 i.2 p.1.1) 0 *
      (M.toricChart i.1 i.2 p.1.1) 1 *
      (M.toricChart i.1 i.2 p.1.1) 2‖ < r
    rw [← M.toricChart_t i.1 i.2 p.1.1 p.2]
    exact mem_ball_zero_iff.mp p.1.2⟩
  invFun z := by
    have hz : (z : ComplexModel) ∈ (M.toricChart i.1 i.2).target := by
      rw [M.toricChart_target]
      exact Set.mem_univ _
    refine ⟨⟨(M.toricChart i.1 i.2).toPartialEquiv.symm z, ?_⟩,
      (M.toricChart i.1 i.2).map_target hz⟩
    rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
    rw [M.toricChart_t i.1 i.2
      ((M.toricChart i.1 i.2).toPartialEquiv.symm z)
      ((M.toricChart i.1 i.2).map_target hz)]
    rw [(M.toricChart i.1 i.2).toPartialEquiv.right_inv hz]
    exact z.2
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (M.toricChart i.1 i.2).toPartialEquiv.left_inv p.2
  right_inv z := by
    apply Subtype.ext
    have hz : (z : ComplexModel) ∈ (M.toricChart i.1 i.2).target := by
      rw [M.toricChart_target]
      exact Set.mem_univ _
    exact (M.toricChart i.1 i.2).toPartialEquiv.right_inv hz
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (M.toricChart i.1 i.2).toOpenPartialHomeomorph.continuousOn_toFun.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
    intro p
    exact p.2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply (M.toricChart i.1 i.2).toOpenPartialHomeomorph.continuousOn_invFun.comp_continuous
      continuous_subtype_val
    intro z
    change (z : ComplexModel) ∈ (M.toricChart i.1 i.2).target
    rw [M.toricChart_target]
    exact Set.mem_univ _

public theorem localCarrierToricChartSet_contractible
    (M : Model) {r : ℝ} (hr : 0 < r) (i : Bool × ToricLattice) :
    ContractibleSpace (localCarrierToricChartSet M r i) := by
  let _ : ContractibleSpace (baseConeCuspRegion r) :=
    baseConeCuspRegion_contractible r hr
  exact (localCarrierToricChartHomeomorph M r i).contractibleSpace

/-- The radius-cut affine toric charts cover the local cusp carrier. -/
public theorem localCarrierToricChartSet_cover (M : Model) (r : ℝ) :
    Set.univ ⊆ ⋃ i : Bool × ToricLattice, localCarrierToricChartSet M r i := by
  intro p _
  obtain ⟨upper, v, hp⟩ := M.toricChart_cover p.1
  rw [Set.mem_iUnion]
  exact ⟨(upper, v), hp⟩

/-- Every point of the punctured local carrier belongs to every affine toric chart. -/
public theorem puncturedLocalCarrier_mem_localCarrierToricChartSet
    (M : Model) (r : ℝ)
    (p : {q : LocalCarrier M r // M.t q ≠ 0})
    (i : Bool × ToricLattice) :
    p.1 ∈ localCarrierToricChartSet M r i := by
  have hp : p.1.1 ∈ Set.range M.torusEmbedding := by
    rw [M.torus_range]
    exact p.2
  obtain ⟨x, hx⟩ := hp
  change p.1.1 ∈ (M.toricChart i.1 i.2).source
  rw [← hx]
  exact M.torus_mem_toricChart i.1 i.2 x

/-- Pairwise intersections of radius-cut affine charts are path connected: they are open and
contain the same connected dense torus locus. -/
public theorem localCarrierToricChartSet_pair_isPathConnected
    (M : Model) {r : ℝ} (hr : 0 < r) (i j : Bool × ToricLattice) :
    IsPathConnected
      (localCarrierToricChartSet M r i ∩ localCarrierToricChartSet M r j) := by
  let _ := M.topology
  let _ := M.charts
  let _ : ChartedSpace ComplexModel (LocalCarrier M r) :=
    (cuspNeighborhood M r).instChartedSpace
  let _ : LocallyPathConnectedSpace (LocalCarrier M r) :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel (LocalCarrier M r)
  let D : Set (LocalCarrier M r) := {p | M.t p ≠ 0}
  let _ : PathConnectedSpace D := puncturedLocalCarrier_pathConnected M hr
  have hD : IsConnected D := isConnected_iff_connectedSpace.mpr inferInstance
  have hdense : Dense D := puncturedLocalCarrier_dense M r
  have hsubset : D ⊆
      localCarrierToricChartSet M r i ∩ localCarrierToricChartSet M r j := by
    intro p hp
    exact ⟨
      puncturedLocalCarrier_mem_localCarrierToricChartSet M r ⟨p, hp⟩ i,
      puncturedLocalCarrier_mem_localCarrierToricChartSet M r ⟨p, hp⟩ j⟩
  have hconnected : IsConnected
      (localCarrierToricChartSet M r i ∩ localCarrierToricChartSet M r j) :=
    hD.subset_closure hsubset (by
      rw [hdense.closure_eq]
      exact Set.subset_univ _)
  exact ((localCarrierToricChartSet_isOpen M r i).inter
    (localCarrierToricChartSet_isOpen M r j)).isConnected_iff_isPathConnected.mp hconnected

/-- At a point of its dense torus locus, the raw local toric cusp carrier has trivial
fundamental group.  This is the direct open-cover consequence of the contractible affine fan
charts and their path-connected overlaps. -/
public theorem localCarrier_fundamentalGroup_subsingleton
    (M : Model) {r : ℝ} (hr : 0 < r)
    (b : {p : LocalCarrier M r // M.t p ≠ 0}) :
    Subsingleton (FundamentalGroup (LocalCarrier M r) b.1) := by
  let U : (Bool × ToricLattice) → Set (LocalCarrier M r) :=
    localCarrierToricChartSet M r
  have hb : ∀ i, b.1 ∈ U i :=
    puncturedLocalCarrier_mem_localCarrierToricChartSet M r b
  have hgenerate :
      Subgroup.closure (openCoverLoopClasses U b.1) = ⊤ :=
    openCoverLoopClasses_generate U b.1
      (localCarrierToricChartSet_isOpen M r)
      (localCarrierToricChartSet_cover M r) hb
      (localCarrierToricChartSet_pair_isPathConnected M hr)
  have hgenerators : ∀ g ∈ openCoverLoopClasses U b.1, g = 1 := by
    intro g hg
    obtain ⟨i, L, hL, rfl⟩ := hg
    let bU : U i := ⟨b.1, hb i⟩
    let LU : Path bU bU :=
      { toFun := fun t ↦ ⟨L t, hL ⟨t, rfl⟩⟩
        continuous_toFun :=
          Continuous.subtype_mk L.continuous fun t ↦ hL ⟨t, rfl⟩
        source' := Subtype.ext L.source
        target' := Subtype.ext L.target }
    let inc : C(U i, LocalCarrier M r) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let _ : ContractibleSpace (U i) :=
      localCarrierToricChartSet_contractible M hr i
    have htrivial : openCoverLoopClass LU = 1 := Subsingleton.elim _ _
    have hmapped := congrArg (FundamentalGroup.map inc bU) htrivial
    rw [map_one] at hmapped
    rw [FundamentalGroup.map_apply] at hmapped
    unfold openCoverLoopClass at hmapped
    rw [← Path.Homotopic.Quotient.mk_map] at hmapped
    have hpath : LU.map continuous_subtype_val = L := by
      apply Path.ext
      funext t
      rfl
    rw [hpath] at hmapped
    exact hmapped
  have hclosure : Subgroup.closure (openCoverLoopClasses U b.1) ≤ ⊥ := by
    apply (Subgroup.closure_le _).2
    intro g hg
    exact Subgroup.mem_bot.mpr (hgenerators g hg)
  constructor
  intro g h
  have hg : g ∈ Subgroup.closure (openCoverLoopClasses U b.1) := by
    rw [hgenerate]
    trivial
  have hh : h ∈ Subgroup.closure (openCoverLoopClasses U b.1) := by
    rw [hgenerate]
    trivial
  have hg_one : g = 1 := Subgroup.mem_bot.mp (hclosure hg)
  have hh_one : h = 1 := Subgroup.mem_bot.mp (hclosure hh)
  exact hg_one.trans hh_one.symm

/-- The raw punctured-locus inclusion surjects on fundamental groups. -/
public def puncturedLocalCarrierInclusion (M : Model) (r : ℝ) :
    C({p : LocalCarrier M r // M.t p ≠ 0}, LocalCarrier M r) :=
  ⟨Subtype.val, continuous_subtype_val⟩

public theorem puncturedLocalCarrierInclusion_fundamentalGroup_surjective
    (M : Model) {r : ℝ} (hr : 0 < r)
    (b : {p : LocalCarrier M r // M.t p ≠ 0}) :
    Function.Surjective
      (FundamentalGroup.map (puncturedLocalCarrierInclusion M r) b) := by
  let _ : Subsingleton (FundamentalGroup (LocalCarrier M r)
      ((puncturedLocalCarrierInclusion M r) b)) := by
    change Subsingleton (FundamentalGroup (LocalCarrier M r) b.1)
    exact localCarrier_fundamentalGroup_subsingleton M hr b
  intro g
  refine ⟨1, ?_⟩
  rw [map_one]
  exact Subsingleton.elim _ _

/-- The restricted phase-action quotient projection is a quotient covering.  This is obtained
directly from the full local covering by pulling its disjoint neighborhoods back to the invariant
punctured subtype. -/
public theorem puncturedLocalCusp_quotient_isQuotientCoveringMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := puncturedPsiAction W
    IsQuotientCoveringMap
      (Quotient.mk (puncturedPsiOrbitRel W) :
        {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
          puncturedLocalCuspQuotient W)
      (Multiplicative ParameterLattice) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let hf := W.localWitness.quotient_isQuotientCoveringMap
  let _ : MulAction (Multiplicative ParameterLattice)
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedPsiAction W
  refine
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_smul := ?_
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro gamma
    apply Continuous.subtype_mk
    change Continuous (fun p :
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} ↦
        C.psiMap (Multiplicative.toAdd gamma) p.1)
    exact (C.psiMap_holomorphic (Multiplicative.toAdd gamma)).continuous.comp
      continuous_subtype_val
  · intro p q
    rw [Quotient.eq]
    rfl
  · intro p
    have hsmul (gamma : Multiplicative ParameterLattice)
        (q : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
        ((gamma • q :
          {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
            LocalCarrier M W.localWitness.radius) = gamma • q.1 := by
      change C.psiMap (Multiplicative.toAdd gamma) q.1 =
        (C.toCuspActionData W.localWitness.fixedPoint).psiMap
          (Multiplicative.toAdd gamma) q.1
      exact C.psiMap_eq_generic W.localWitness.fixedPoint _ _
    obtain ⟨V, hV, hdisjoint⟩ := hf.disjoint p.1
    refine ⟨Subtype.val ⁻¹' V,
      continuousAt_subtype_val.preimage_mem_nhds hV, ?_⟩
    intro gamma hmeet
    apply hdisjoint gamma
    obtain ⟨x, ⟨y, hy, hxy⟩, hx⟩ := hmeet
    refine ⟨x.1, ⟨y.1, hy, ?_⟩, hx⟩
    exact (hsmul gamma y).symm.trans (congrArg Subtype.val hxy)

/-- The actual punctured cusp collar includes into the toric filling surjectively on fundamental
groups. -/
public theorem puncturedLocalCuspToFilling_fundamentalGroup_surjective
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (b : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨puncturedLocalCuspToFilling W,
          puncturedLocalCuspToFilling_continuous W⟩ :
          C(puncturedLocalCuspQuotient W, actualLocalCuspFilling W))
        (Quotient.mk _ b)) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedPsiAction W
  let hfS : IsQuotientCoveringMap
      (Quotient.mk (puncturedPsiOrbitRel W) :
        {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
          puncturedLocalCuspQuotient W)
      (Multiplicative ParameterLattice) :=
    puncturedLocalCusp_quotient_isQuotientCoveringMap W
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let hfV : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius)) :
        LocalCarrier M W.localWitness.radius → actualLocalCuspFilling W)
      (Multiplicative ParameterLattice) :=
    W.localWitness.quotient_isQuotientCoveringMap
  let sourceMap : C(
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0},
      LocalCarrier M W.localWitness.radius) :=
    puncturedLocalCarrierInclusion M W.localWitness.radius
  let targetMap : C(puncturedLocalCuspQuotient W, actualLocalCuspFilling W) :=
    ⟨puncturedLocalCuspToFilling W,
      puncturedLocalCuspToFilling_continuous W⟩
  have hcomm (p :
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
      targetMap (Quotient.mk _ p) = Quotient.mk _ (sourceMap p) := by
    exact puncturedLocalCuspToFilling_mk W p
  have hequiv (gamma : Multiplicative ParameterLattice)
      (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
      sourceMap (gamma • p) = gamma • sourceMap p := by
    change C.psiMap (Multiplicative.toAdd gamma) p.1 =
      (C.toCuspActionData W.localWitness.fixedPoint).psiMap
        (Multiplicative.toAdd gamma) p.1
    exact C.psiMap_eq_generic W.localWitness.fixedPoint _ _
  let _ : PathConnectedSpace
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_pathConnected M W.localWitness.radius_pos
  let _ : PathConnectedSpace (LocalCarrier M W.localWitness.radius) :=
    localCarrier_pathConnected M W.localWitness.radius_pos
  have hsource : Function.Surjective
      (FundamentalGroup.map sourceMap b) := by
    simpa [sourceMap] using
      puncturedLocalCarrierInclusion_fundamentalGroup_surjective
        M W.localWitness.radius_pos b
  have hmapOfEq := quotientCovering_equivariant_map_fundamentalGroup_surjective
    hfS hfV sourceMap targetMap hcomm hequiv b hsource
  exact fundamentalGroup_map_surjective_of_mapOfEq_surjective
    targetMap (Quotient.mk _ b) (Quotient.mk _ (sourceMap b))
      (hcomm b) hmapOfEq

/-- Basepoint-free form of cusp collar surjectivity. -/
public theorem puncturedLocalCuspToFilling_fundamentalGroup_surjective_at
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (q : puncturedLocalCuspQuotient W) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨puncturedLocalCuspToFilling W,
          puncturedLocalCuspToFilling_continuous W⟩ :
          C(puncturedLocalCuspQuotient W, actualLocalCuspFilling W)) q) := by
  induction q using Quotient.inductionOn with
  | _ b => exact puncturedLocalCuspToFilling_fundamentalGroup_surjective W b

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
