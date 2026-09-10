module

public import SphereSixComplex.Paper.Topology.ConstructedA2CellularEdgeLoops
public import SphereSixComplex.Paper.Topology.CuspCellularCycleCoordinates

@[expose] public section
noncomputable section
open CategoryTheory
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex StandardCircleHomologyLiftDegree
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCentralCellularEdgeLoop_homology_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation)
    (I : let _ := (constructedCentralCellAtlas W).cwComplex
      StandardA2ToricCellularIncidenceData (fun _ ↦ Equiv.refl _)
        (T.normalized.objectwiseModel (ActualLocalCuspCentralOrbitQuotient W)))
    (j k : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    I.integralSingularHomologyOneEquiv
      ((HomologicalComplex.homologyMap (cwIntegralSingularChainMapObj
        (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1).hom
        (loopHomologyClass ((constructedCentralCellularEdgePath W j).trans
          (constructedCentralCellularEdgePath W k).symm))) =
      fun i : Fin 2 ↦ (if i.castSucc = j then 1 else 0) -
        (if i.castSucc = k then 1 else 0) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  dsimp only
  refine (I.homologyOne_skeletal T.normalized (ActualLocalCuspCentralOrbitQuotient W)
    (fun _ ↦ Equiv.refl _) _).trans ?_
  have h := constructedCentralCellularEdgeLoop_relative_class W T j k
  funext i
  change ((T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1).symm _)
    i.castSucc = _
  erw [h]
  change ((Finsupp.single j 1 - Finsupp.single k 1 : Fin 3 →₀ ℤ) i.castSucc) = _
  simp only [Finsupp.sub_apply, Finsupp.single_apply]
  simp only [eq_comm]

public theorem constructedCentralCellularEdgeLoop_basis_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation)
    (I : let _ := (constructedCentralCellAtlas W).cwComplex
      StandardA2ToricCellularIncidenceData (fun _ ↦ Equiv.refl _)
        (T.normalized.objectwiseModel (ActualLocalCuspCentralOrbitQuotient W)))
    (j : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    I.integralSingularHomologyOneEquiv
      ((HomologicalComplex.homologyMap (cwIntegralSingularChainMapObj
        (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1).hom
        (loopHomologyClass ((constructedCentralCellularEdgePath W j.castSucc).trans
          (constructedCentralCellularEdgePath W 2).symm))) = Pi.single j 1 := by
  refine (constructedCentralCellularEdgeLoop_homology_coordinates W T I j.castSucc 2).trans ?_
  funext i
  fin_cases i <;> fin_cases j <;> simp

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
