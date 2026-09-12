module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepRelativeAction
public import SphereSixComplex.Prerequisites.Topology.CylinderRelativePrismNaturality
public import SphereSixComplex.Prerequisites.Topology.CellularPathComparison

@[expose] public section
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction CuspFilling CuspPeriodExpansion
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepEdgeBasePair
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    CWTopologicalPairMap (cylinderBaseInclusion (cwBallBoundarySet 1))
      (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let P := integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 i
  exact
    { left := (TopCat.isoOfHomeo (cwBoundaryNestedHomeomorph 1)).inv ≫ P.boundaryMap
      right := P.diskMap
      comm := by ext x : 1; rfl }

public theorem phaseSweepEdgeBasePair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3)
    (b : CWCharacteristicClosedBall 1) :
    ((phaseSweepEdgeBasePair W i).right b).1 = constructedCentralOneCell W i b.1 := rfl

public theorem phaseSweepEdgeBasePair_relativeChainMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    (cwNestedBoundaryRelativeIso 1).hom ≫
      cwRelativeIntegralSingularChainMapOfPair (phaseSweepEdgeBasePair W i) =
        (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 i).relativeChainMap := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel
    (cwIntegralSingularChainMapObj (cwCharacteristicBoundaryInclusion 1)))
  change cwRelativeIntegralSingularChainProjection _ ≫ _ =
    cwRelativeIntegralSingularChainProjection _ ≫ _
  rw [← Category.assoc]
  have hn : cwRelativeIntegralSingularChainProjection (cwCharacteristicBoundaryInclusion 1) ≫
      (cwNestedBoundaryRelativeIso 1).hom =
        cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion (cwBallBoundarySet 1)) := by
    change cokernel.π _ ≫ (cwNestedBoundaryRelativeIso 1).hom = _
    dsimp only [cwNestedBoundaryRelativeIso, cokernel.mapIso_hom]
    erw [cokernel.π_desc]
    rfl
  rw [hn, cwRelativeIntegralSingularChainProjection_natural]
  change _ = cwRelativeIntegralSingularChainProjection _ ≫
    cwRelativeIntegralSingularChainMapOfPair _
  rw [cwRelativeIntegralSingularChainProjection_natural]
  rfl

public theorem phaseSweepEdgeBasePair_orientedClass
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepEdgeBasePair W i)) 1
      (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 (cwOrientedIntervalClass.hom 1)) =
        T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single i 1) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  change (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 ≫
    homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepEdgeBasePair W i)) 1) _ = _
  rw [← homologyMap_comp, phaseSweepEdgeBasePair_relativeChainMap]
  have h := T.normalized.cellBasis_single (ActualLocalCuspCentralOrbitQuotient W) 1 i
  rw [T.normalized_diskOrientation_one, normalizedIntervalDiskOrientation_symm_one] at h
  exact h.symm

end SphereSixComplex.Geometry.CuspCollar
