module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralAttachment
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralCompactAction
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCover

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

instance centralBoundary_pathConnectedSpace
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PathConnectedSpace (centralBoundary W) := by
  let _ := CentralBoundary.contractibleSpace_reciprocalPart W
  have hf : IsPathConnected CentralBoundary.finitePart :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hr : IsPathConnected CentralBoundary.reciprocalPart :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hi : (CentralBoundary.finitePart ∩ CentralBoundary.reciprocalPart).Nonempty := by
    refine ⟨CentralBoundary.mk 0 (1 : ℂ), ?_, ?_⟩
    · rw [CentralBoundary.mk_mem_finitePart]
      exact OnePoint.coe_ne_infty _
    · rw [CentralBoundary.mk_mem_reciprocalPart]
      simp
  let _ : PathConnectedSpace CentralBoundary.Spheres :=
    pathConnectedSpace_iff_univ.mpr
      (CentralBoundary.finitePart_union_reciprocalPart ▸ hf.union hr hi)
  exact (CentralBoundary.homeomorph W).surjective.pathConnectedSpace
    (CentralBoundary.homeomorph W).continuous

public theorem centralCompactOrbitMap_centralDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle)
    (p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle)) :
    centralCompactOrbitMap W k (centralDiskMap W p) = centralDiskMap W (p.1, k * p.2) :=
  by
    change centralCompactOrbitMap W k (effectivePhaseCentralOrbit W (_ * p.2) _) =
      effectivePhaseCentralOrbit W (_ * (k * p.2)) _
    rw [centralCompactOrbitMap_effectivePhase, mul_left_comm]

@[simp] public theorem centralCompactOrbitMap_origin
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (upper : Bool) :
    centralCompactOrbitMap W k (constructedCentralOriginOrbit W upper) =
      constructedCentralOriginOrbit W upper := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  change carrierTorusActionFun _ (inclusion (upper, 0) 0) = inclusion (upper, 0) 0
  rw [carrierTorusActionFun_inclusion, mul_zero]

public theorem centralCompactOrbitMap_mem_boundary_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (x : ActualLocalCuspCentralOrbitQuotient W) :
    centralCompactOrbitMap W k x ∈ centralBoundary W ↔ x ∈ centralBoundary W := by
  obtain ⟨p, rfl⟩ := centralDiskMap_surjective W x
  rw [centralCompactOrbitMap_centralDiskMap, centralDiskMap_mem_boundary_iff,
    centralDiskMap_mem_boundary_iff]

public def centralBoundaryPhaseMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C((Fin 2 → Circle) × centralBoundary W, centralBoundary W) where
  toFun p := ⟨centralCompactOrbitMap W p.1 p.2.1,
    (centralCompactOrbitMap_mem_boundary_iff W p.1 p.2.1).mpr p.2.2⟩
  continuous_toFun :=
    ((continuous_centralCompactOrbitMap W).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

public theorem centralAttachingMap_eq_phase
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hp : ‖p.1‖ = 1) (k : Fin 2 → Circle) :
    centralAttachingMap W ⟨(p, k), hp⟩ =
      centralBoundaryPhaseMap W (k, centralAttachingMap W ⟨(p, 1), hp⟩) := by
  apply Subtype.ext
  change centralDiskMap W (p, k) = centralCompactOrbitMap W k (centralDiskMap W (p, 1))
  rw [centralCompactOrbitMap_centralDiskMap, mul_one]

public def centralBoundaryCircleSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (phase : C(UnitAddCircle, Fin 2 → Circle)) :
    C(UnitAddCircle × centralBoundary W, centralBoundary W) :=
  (centralBoundaryPhaseMap W).comp
    ⟨fun p ↦ (phase p.1, p.2),
      (phase.continuous.comp continuous_fst).prodMk continuous_snd⟩

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
end
