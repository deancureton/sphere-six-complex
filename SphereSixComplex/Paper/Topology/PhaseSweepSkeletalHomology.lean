module
public import SphereSixComplex.Paper.Topology.RechartSkeletalComparison
public import SphereSixComplex.Prerequisites.Topology.CellularSkeletalComparison
public import SphereSixComplex.Paper.Topology.CuspPhaseSweepAtlas

@[expose] public section
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods StandardA2ToricCentralFiberCellAtlas
open InfiniteA2Toric InfiniteA2Toric.Construction
open InfiniteA2Toric CuspPeriodExpansion
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCellAtlas_d_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    (constructedCentralCellAtlas W).skeletalComplex.d 2 1 = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  change integralCWRelativeBoundary (ActualLocalCuspCentralOrbitQuotient W) 1 = 0
  exact T.relativeBoundary_eq_zero_of_attachingDegree_eq_zero _ 1
    (constructedA2TwoCell_attachingDegree_zero W T)

public theorem constructedCellAtlas_d_three
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    (constructedCentralCellAtlas W).skeletalComplex.d 3 2 = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  change integralCWRelativeBoundary (ActualLocalCuspCentralOrbitQuotient W) 2 = 0
  exact T.relativeBoundary_eq_zero_of_attachingDegree_eq_zero _ 2
    (constructedA2ThreeCell_attachingDegree_zero W T)

public theorem phaseSweepCellAtlas_closedImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : CuspWCellIndex n) :
    (constructedCentralCellAtlas W).cellMap n i '' Metric.closedBall 0 1 =
      (phaseSweepCellAtlas W).cellMap n i '' Metric.closedBall 0 1 :=
  (phaseSweepCellMap_closedImage W n i).symm

public theorem phaseSweepCellAtlas_d_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    (phaseSweepCellAtlas W).skeletalComplex.d 2 1 = 0 :=
  rechartSkeletal_d_zero T _ _ (phaseSweepCellAtlas_closedImage W) 2 1
    (constructedCellAtlas_d_two W T)

public theorem phaseSweepCellAtlas_d_three
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    (phaseSweepCellAtlas W).skeletalComplex.d 3 2 = 0 :=
  rechartSkeletal_d_zero T _ _ (phaseSweepCellAtlas_closedImage W) 3 2
    (constructedCellAtlas_d_three W T)

public def phaseSweepHomologyTwoToRelativeEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W) ≃+
      integralCWRelativeCellObject (ActualLocalCuspCentralOrbitQuotient W) 2 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let K := (phaseSweepCellAtlas W).skeletalComplex
  exact (T.homologyEquiv (ActualLocalCuspCentralOrbitQuotient W) 2).symm.trans
    (homologyIsoOfAdjacentZeros K 1 (phaseSweepCellAtlas_d_three W T)
      (phaseSweepCellAtlas_d_two W T)).addCommGroupIsoToAddEquiv

public def phaseSweepHomologyTwoCellEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W) ≃+ (Fin 4 → ℤ) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let _ : Finite (Topology.CWComplex.cell
      (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W)) 2) := by
    change Finite (Fin 4)
    infer_instance
  exact (phaseSweepHomologyTwoToRelativeEquiv W T).trans
    ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm.trans
      Finsupp.addEquivFunOnFinite)

public theorem phaseSweepHomologyTwoToRelativeEquiv_skeletal
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ x : (cwIntegralSingularChainComplexObj
      (TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 3))).homology 2,
    phaseSweepHomologyTwoToRelativeEquiv W T
      ((HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj
          (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 3)) 2).hom x) =
      (HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection
          (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2)) 2).hom x := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let X := ActualLocalCuspCentralOrbitQuotient W
  let K := (phaseSweepCellAtlas W).skeletalComplex
  dsimp only
  intro x
  rw [← T.homologyEquiv_skeletal_apply X 2 x]
  change (homologyIsoOfAdjacentZeros K 1 (phaseSweepCellAtlas_d_three W T)
      (phaseSweepCellAtlas_d_two W T)).hom.hom
    ((T.homologyEquiv X 2).symm ((T.homologyEquiv X 2) _)) = _
  rw [AddEquiv.symm_apply_apply]
  have hc : integralCWSkeletalHomologyToCellular X 2 ≫
      (homologyIsoOfAdjacentZeros K 1 (phaseSweepCellAtlas_d_three W T)
        (phaseSweepCellAtlas_d_two W T)).hom =
      HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X 2)) 2 := by
    dsimp only [integralCWSkeletalHomologyToCellular]
    erw [Category.assoc, homologyIsoOfAdjacentZeros_π]
    exact K.liftCycles_i _ _ _ _
  exact ConcreteCategory.congr_hom hc x


end SphereSixComplex.Geometry.CuspCollar
