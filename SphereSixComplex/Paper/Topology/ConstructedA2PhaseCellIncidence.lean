module

public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas
public import SphereSixComplex.Prerequisites.Topology.CellularContractibleAttachingMap

@[expose] public section
noncomputable section
open Set Topology CategoryTheory

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCentralOneCell_injOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Set.InjOn (constructedCentralOneCell W i) (Metric.closedBall 0 1) := by
  fin_cases i
  · exact constructedCentralEdgeZeroOrbit_injOn_closedBall W
  · exact constructedCentralEdgeOneOrbit_injOn_closedBall W
  · exact constructedCentralEdgeTwoOrbit_injOn_closedBall W

public theorem constructedCentralPhaseTwoCell_boundary_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.sphere 0 1) :
    constructedCentralPhaseTwoCell W i x ∈
      constructedCentralOneCell W i '' Metric.closedBall 0 1 := by
  obtain ⟨t, ht, he⟩ := constructedCentralPhaseFaceCarrier_boundary_mem_edge i x hx
  refine ⟨t, ht, ?_⟩
  have hp : constructedCentralEdgeCellPoint W i t = constructedCentralPhaseCellPoint W i x := by
    apply Subtype.ext
    apply Subtype.ext
    fin_cases i <;> exact he
  have hq := congrArg (Quotient.mk (MulAction.orbitRel
    (Multiplicative CuspFilling.ParameterLattice)
    (actualLocalCuspCentralSubMulAction W))) hp
  fin_cases i <;> exact hq

public theorem constructedCentralPhaseTwoCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 1 i.succ j = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  let _ : ContractibleSpace (CWCharacteristicClosedBall 1) :=
    (convex_closedBall (0 : Fin 1 → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let v := (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 i).diskMap
  apply T.attachingDegree_zero_of_boundary_mem_embedded_contractible
    (ActualLocalCuspCentralOrbitQuotient W) 1 (by decide) i.succ j v
  · apply v.hom.continuous.isClosedEmbedding ?_ |>.isEmbedding
    intro x y hxy
    apply Subtype.ext
    exact constructedCentralOneCell_injOn_closedBall W i x.2 y.2
      (congrArg Subtype.val hxy)
  · intro x
    obtain ⟨t, ht, he⟩ := constructedCentralPhaseTwoCell_boundary_mem_edge W i x.1 x.2
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change constructedCentralOneCell W i t = constructedCentralCellMap W 2 i.succ x.1
    fin_cases i <;> exact he

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
