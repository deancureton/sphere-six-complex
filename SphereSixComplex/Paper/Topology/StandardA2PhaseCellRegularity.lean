module

public import SphereSixComplex.Paper.Topology.StandardA2PhaseCellDisjointness

@[expose] public section
noncomputable section
open Set Matrix Topology
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Geometry.InfiniteA2Toric
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

private theorem isEmbedding_restrict_of_compact_boundary_separation
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (s K : Set X) (hK : IsCompact K) (hsK : s ⊆ K)
    (hf : ContinuousOn f K) (hinj : Set.InjOn f s)
    (hboundary : Disjoint (f '' (K \ s)) (f '' s)) :
    Topology.IsEmbedding (s.domRestrict f) := by
  let t : Set Y := f '' s
  let g : s → t := Set.codRestrict (s.domRestrict f) t (fun x ↦ ⟨x, x.2, rfl⟩)
  have hfs : Continuous (s.domRestrict f) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono hsK)
  have hgcont : Continuous g := hfs.codRestrict _
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.2 y.2
    exact congrArg Subtype.val hxy
  have hgclosed : IsClosedMap g := by
    intro A hA
    let L : Set X := closure (Subtype.val '' A)
    have hKclosed : IsClosed K := hK.isClosed
    have hvalAK : Subtype.val '' A ⊆ K := by
      rintro x ⟨a, ha, rfl⟩
      exact hsK a.2
    have hLK : L ⊆ K := closure_minimal hvalAK hKclosed
    have hLcompact : IsCompact L :=
      hK.of_isClosed_subset isClosed_closure hLK
    have hfL : ContinuousOn f L := hf.mono hLK
    have hfLclosed : IsClosed (f '' L) :=
      (hLcompact.image_of_continuousOn hfL).isClosed
    apply isClosed_induced_iff.mpr
    refine ⟨f '' L, hfLclosed, ?_⟩
    ext z
    constructor
    · rintro ⟨x, hxL, hfx⟩
      have hxs : x ∈ s := by
        by_contra hxs
        have hxBoundary : f x ∈ f '' (K \ s) := ⟨x, ⟨hLK hxL, hxs⟩, rfl⟩
        have hzInterior : f x ∈ f '' s := by
          rw [hfx]
          exact z.2
        exact Set.disjoint_left.mp hboundary hxBoundary hzInterior
      have hxClosure : (⟨x, hxs⟩ : s) ∈ closure A :=
        closure_subtype.mpr hxL
      rw [hA.closure_eq] at hxClosure
      refine ⟨⟨x, hxs⟩, hxClosure, ?_⟩
      apply Subtype.ext
      exact hfx
    · rintro ⟨x, hxA, rfl⟩
      refine ⟨x, subset_closure ⟨x, hxA, rfl⟩, rfl⟩
  have hg : Topology.IsEmbedding g :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hgcont hginj hgclosed).isEmbedding
  have hcomp := Topology.IsEmbedding.subtypeVal.comp hg
  change Topology.IsEmbedding (fun x : s ↦ f x)
  convert hcomp using 1
  funext x
  rfl

public theorem constructedCentralPhaseTwoCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    (constructedCentralPhaseTwoCell W i).source = Metric.ball 0 1 := by
  fin_cases i <;> rfl

public theorem constructedCentralPhaseTwoCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    ContinuousOn (constructedCentralPhaseTwoCell W i) (Metric.closedBall 0 1) := by
  fin_cases i
  · exact constructedCentralPhaseTwoCellZero_continuousOn W
  · exact constructedCentralPhaseTwoCellOne_continuousOn W
  · exact constructedCentralPhaseTwoCellTwo_continuousOn W

public theorem constructedCentralPhaseFaceCarrier_boundary_mem_edge
    (i : Fin 3) (x : Fin 2 → ℝ) (hx : x ∈ Metric.sphere 0 1) :
    constructedCentralPhaseFaceCarrier i x ∈
      constructedCentralEdgeCarrier i '' Metric.closedBall 0 1 := by
  obtain ⟨t, ht, he⟩ := constructedCentralPhaseFaceZeroCarrier_boundary_mem_edgeZero x hx
  refine ⟨t, ht, ?_⟩
  fin_cases i
  · exact he
  · exact (a2CyclicCarrier_constructedCentralEdgeZeroCarrier t).symm.trans
      ((congrArg a2CyclicCarrier he).trans
        (a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier x))
  · exact (a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier t).symm.trans
      ((congrArg (fun p ↦ a2CyclicCarrier (a2CyclicCarrier p)) he).trans
        (a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier x))

public theorem constructedCentralPhaseTwoCell_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    MapsTo (constructedCentralPhaseTwoCell W i) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) := by
  intro x hx
  obtain ⟨t, ht, he⟩ := constructedCentralPhaseFaceCarrier_boundary_mem_edge i x hx
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨i, t, ht, ?_⟩
  have hp : constructedCentralEdgeCellPoint W i t =
      constructedCentralPhaseCellPoint W i x := by
    apply Subtype.ext
    apply Subtype.ext
    fin_cases i <;> exact he
  have hq := congrArg (Quotient.mk (MulAction.orbitRel
    (Multiplicative ParameterLattice) (actualLocalCuspCentralSubMulAction W))) hp
  fin_cases i <;> exact hq

public theorem constructedCentralPhaseTwoCell_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Topology.IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (constructedCentralPhaseTwoCell W i)) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  apply isEmbedding_restrict_of_compact_boundary_separation
    (constructedCentralPhaseTwoCell W i) (Metric.ball 0 1) (Metric.closedBall 0 1)
    (isCompact_closedBall 0 1) Metric.ball_subset_closedBall
    (constructedCentralPhaseTwoCell_continuousOn W i)
  · rw [← constructedCentralPhaseTwoCell_source_eq W i]
    exact (constructedCentralPhaseTwoCell W i).injOn
  · rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ hy
    have hs : x ∈ Metric.sphere 0 1 := by
      simpa [Metric.closedBall_sdiff_ball] using hx
    exact Set.disjoint_left.mp (constructedCentralPhaseTwoCell_oneSkeleton_disjoint W i)
      hy (constructedCentralPhaseTwoCell_mapsTo_oneSkeleton W i hs)

public theorem constructedCentralPhaseTwoCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    ContinuousOn (constructedCentralPhaseTwoCell W i).symm
      (constructedCentralPhaseTwoCell W i).target := by
  let e := constructedCentralPhaseTwoCell W i
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 := fun q ↦
    ⟨e.symm q, by rw [← constructedCentralPhaseTwoCell_source_eq W i]; exact e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (constructedCentralPhaseTwoCell_isEmbedding W i).continuous_iff.mpr
    have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (constructedCentralPhaseTwoCell W i) ∘ lift =
        (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 2 → ℝ))
  exact continuous_subtype_val.comp hlift

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
