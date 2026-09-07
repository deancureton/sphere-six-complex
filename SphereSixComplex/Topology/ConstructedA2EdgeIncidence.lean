module

public import SphereSixComplex.Topology.ConstructedA2CellAtlas
public import SphereSixComplex.Topology.CellularEdgeBoundary

@[expose] public section
noncomputable section
open CategoryTheory Set
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCentralCellAtlas_edge_left
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j : Fin 3) :
    constructedCentralCellMap W 1 j (fun _ ↦ -1) =
      constructedCentralCellMap W 0 (0 : Fin 2) 0 := by
  fin_cases j
  · exact constructedCentralEdgeZeroOrbit_negOne W
  · exact constructedCentralEdgeOneOrbit_negOne W
  · exact constructedCentralEdgeTwoOrbit_negOne W

public theorem constructedCentralCellAtlas_edge_right
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j : Fin 3) :
    constructedCentralCellMap W 1 j (fun _ ↦ 1) =
      constructedCentralCellMap W 0 (1 : Fin 2) 0 := by
  fin_cases j
  · exact constructedCentralEdgeZeroOrbit_one W
  · exact constructedCentralEdgeOneOrbit_one W
  · exact constructedCentralEdgeTwoOrbit_one W

public theorem constructedCentralCellAtlas_edge_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) (j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 0).symm
      ((integralCWRelativeBoundary (ActualLocalCuspCentralOrbitQuotient W) 0).hom
        (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1
          (Finsupp.single j 1))) = Finsupp.single (1 : Fin 2) (1 : ℤ) - Finsupp.single (0 : Fin 2) 1 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact normalized_cellular_edge_boundary T (ActualLocalCuspCentralOrbitQuotient W)
    j (0 : Fin 2) (1 : Fin 2)
    (Subtype.ext (constructedCentralCellAtlas_edge_left W j))
    (Subtype.ext (constructedCentralCellAtlas_edge_right W j))

public theorem constructedCentralCellAtlas_edge_attachingDegree
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) (j : Fin 3) (i : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.normalized.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 0 j i =
      if i = 0 then -1 else 1 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  have h := congrArg (fun f : Fin 2 →₀ ℤ ↦ f i)
    (constructedCentralCellAtlas_edge_boundary W T j)
  change T.normalized.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 0 j i =
    ((Finsupp.single (1 : Fin 2) (1 : ℤ) - Finsupp.single (0 : Fin 2) 1) : Fin 2 →₀ ℤ) i at h
  change T.normalized.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 0 j i = _
  rw [h]
  fin_cases i <;> norm_num [Finsupp.sub_apply, Finsupp.single_apply]

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
