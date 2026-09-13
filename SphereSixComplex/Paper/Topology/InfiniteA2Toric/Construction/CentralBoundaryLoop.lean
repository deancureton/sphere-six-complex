module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryAction
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCharts
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryLoop
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross

@[expose] public section
noncomputable section
open Set Matrix
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspCombinatorics
open CuspPhaseEstimates StandardCircleHomologyLiftDegree

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCentralOneSkeleton_subset_centralBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralOneSkeleton W ⊆ centralBoundary W := by
  have hzero : (⋃ i : Fin 2, constructedCentralZeroCell W i '' Metric.closedBall 0 1) ⊆
      centralBoundary W := by
    rintro z hz
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    change constructedCentralOriginOrbit W (![false, true] i) ∉ singletonPhaseImage W
    rw [← CentralBoundary.axisOrbit_zero W (![false, true] i) 0]
    exact CentralBoundary.axisOrbit_not_mem_singletonPhaseImage W _ _ _
  have hedge (i : Fin 3) :
      constructedCentralOneCell W i '' Metric.ball 0 1 ⊆ centralBoundary W := by
    rintro z ⟨x, hx, rfl⟩
    fin_cases i
    · apply (CentralBoundary.not_mem_singletonPhaseImage_iff W _).mpr
      change (componentSupport constructedModel (constructedCentralEdgeZeroCarrier x)).ncard ≠ 1
      rw [constructedCentralEdgeZeroCarrier_componentSupport x hx]
      simp [e₁, e₂]
    · apply (CentralBoundary.not_mem_singletonPhaseImage_iff W _).mpr
      change (componentSupport constructedModel (constructedCentralEdgeOneCarrier x)).ncard ≠ 1
      rw [constructedCentralEdgeOneCarrier_componentSupport x hx]
      rw [Set.ncard_pair (by decide : (0 : ToricLattice) ≠ e₂)]
      norm_num
    · apply (CentralBoundary.not_mem_singletonPhaseImage_iff W _).mpr
      change (componentSupport constructedModel (constructedCentralEdgeTwoCarrier x)).ncard ≠ 1
      rw [constructedCentralEdgeTwoCarrier_componentSupport x hx]
      rw [Set.ncard_pair (by decide : (0 : ToricLattice) ≠ e₁)]
      norm_num
  intro z hz
  rcases hz with hz | hz
  · exact hzero hz
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rw [constructedCentralOneCell_closedBall_image_eq] at hi
    exact hi.elim (fun h ↦ hedge i h) (fun h ↦ hzero h)

public def oneSkeletonToCentralBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(constructedCentralOneSkeleton W, centralBoundary W) where
  toFun x := ⟨x.1, constructedCentralOneSkeleton_subset_centralBoundary W x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

public def centralBoundaryHexagonLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Path (oneSkeletonToCentralBoundary W (oneSkeletonOrigin W false))
      (oneSkeletonToCentralBoundary W (oneSkeletonOrigin W false)) :=
  (oneSkeletonHexagonLoop W).map (oneSkeletonToCentralBoundary W).continuous

public theorem centralBoundaryHexagonLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    loopHomologyClass (centralBoundaryHexagonLoop W) = 0 := by
  rw [centralBoundaryHexagonLoop, ← integralSingularHomologyMap_loopHomologyClass,
    oneSkeletonHexagonLoop_homology_zero, map_zero]

open SphereSixComplex.Topology.CircleProductIdentityMappingTorus

public def centralBoundaryCircleSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (phase : C(UnitAddCircle, Fin 2 → Circle)) :
    C(UnitAddCircle × centralBoundary W, centralBoundary W) :=
  (centralBoundaryPhaseMap W).comp
    ⟨fun p ↦ (phase p.1, p.2),
      (phase.continuous.comp continuous_fst).prodMk continuous_snd⟩

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
end
