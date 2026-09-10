module

public import SphereSixComplex.Paper.Topology.ConstructedA2CentralCompactAction
public import SphereSixComplex.Paper.Topology.StandardA2PhaseCellDisjointness
public import SphereSixComplex.Paper.Topology.ActualCuspCentralModelEquivalence

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2CentralCompactMap_support
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle)
    (p : actualLocalCuspCentralSubMulAction W) :
    componentSupport constructedModel ((constructedA2CentralCompactMap W k p).1.1 : Carrier) =
      componentSupport constructedModel (p.1.1 : Carrier) := by
  ext v
  exact constructedModel.torusAction_centralComponent _ v _

public theorem constructedA2CentralCompactOrbitMap_origin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle)
    (b : Bool) :
    constructedA2CentralCompactOrbitMap W k (constructedCentralOriginOrbit W b) =
      constructedCentralOriginOrbit W b := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  change carrierTorusActionFun _ (inclusion (b, 0) 0) = inclusion (b, 0) 0
  rw [carrierTorusActionFun_inclusion, mul_zero]

public theorem constructedA2CentralCompactOrbitMap_support_ge_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle)
    (p : actualLocalCuspCentralSubMulAction W)
    (hp : 2 ≤ (componentSupport constructedModel (p.1.1 : Carrier)).ncard) :
    constructedA2CentralCompactOrbitMap W k (Quotient.mk _ p) ∈
      constructedCentralBoundaryTwoSkeleton W := by
  apply constructedCentral_support_ge_two_mem_boundaryTwoSkeleton W
    (constructedA2CentralCompactMap W k p)
  rwa [constructedA2CentralCompactMap_support]

public theorem constructedA2CentralCompactOrbitMap_phaseCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle)
    (j : Fin 3) (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    constructedA2CentralCompactOrbitMap W k (constructedCentralPhaseFaceOrbit W j x) ∈
      constructedCentralBoundaryTwoSkeleton W := by
  have h := constructedA2CentralCompactOrbitMap_support_ge_two W k
    (constructedCentralPhaseCellPoint W j x) (by
      rw [constructedCentralPhaseCellPoint_support W j x hx, constructedCentralEdgeSupport_ncard])
  fin_cases j <;> exact h

public theorem constructedA2CentralCompactOrbitMap_edgeCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle)
    (j : Fin 3) (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    constructedA2CentralCompactOrbitMap W k (constructedCentralOneCell W j x) ∈
      constructedCentralBoundaryTwoSkeleton W := by
  have h := constructedA2CentralCompactOrbitMap_support_ge_two W k
    (constructedCentralEdgeCellPoint W j x) (by
      rw [constructedCentralEdgeCellPoint_support W j x hx, constructedCentralEdgeSupport_ncard])
  fin_cases j <;> exact h

public theorem constructedA2CentralCompactOrbitMap_zeroCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle)
    (j : Fin 2) (x : Fin 0 → ℝ) :
    constructedA2CentralCompactOrbitMap W k (constructedCentralZeroCell W j x) =
      constructedCentralZeroCell W j x :=
  constructedA2CentralCompactOrbitMap_origin W k _

public theorem constructedA2CentralCompactOrbitMap_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle) :
    Set.MapsTo (constructedA2CentralCompactOrbitMap W k)
      (constructedCentralOneSkeleton W) (constructedCentralBoundaryTwoSkeleton W) := by
  intro z hz
  have hzero : ∀ z ∈ ⋃ j : Fin 2,
      constructedCentralZeroCell W j '' Metric.closedBall 0 1,
      constructedA2CentralCompactOrbitMap W k z ∈ constructedCentralBoundaryTwoSkeleton W := by
    intro z hz
    obtain ⟨j, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    rw [constructedA2CentralCompactOrbitMap_zeroCell]
    exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨j, x, hx, rfl⟩))
  rcases hz with hz | hz
  · exact hzero z hz
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    rw [constructedCentralOneCell_closedBall_image_eq] at hj
    rcases hj with ⟨x, hx, rfl⟩ | hj
    · exact constructedA2CentralCompactOrbitMap_edgeCell W k j x hx
    · exact hzero z hj

public theorem constructedA2CentralCompactOrbitMap_boundaryTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle) :
    Set.MapsTo (constructedA2CentralCompactOrbitMap W k)
      (constructedCentralBoundaryTwoSkeleton W) (constructedCentralBoundaryTwoSkeleton W) := by
  intro z hz
  rcases hz with hz | hz
  · exact constructedA2CentralCompactOrbitMap_oneSkeleton W k hz
  · obtain ⟨j, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    exact constructedA2CentralCompactOrbitMap_phaseCell W k j x hx

end SphereSixComplex.Geometry.InfiniteA2Toric
