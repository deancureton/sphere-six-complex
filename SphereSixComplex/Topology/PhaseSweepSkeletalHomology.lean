module
public import SphereSixComplex.Topology.RechartSkeletalComparison
public import SphereSixComplex.Topology.CellularSkeletalComparison
public import SphereSixComplex.Topology.CuspPhaseSweepAtlas
public import SphereSixComplex.Topology.ConstructedA2DegreeTwoIncidence
public import SphereSixComplex.Topology.ConstructedA2HigherIncidenceProof

@[expose] public section
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods StandardA2ToricCentralFiberCellAtlas
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricModel.Construction
open StandardInfiniteA2ToricModel.Established CuspPeriodExpansion
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCellAtlas_d_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
    (constructedCentralCellAtlas W).skeletalComplex.d 2 1 = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  change integralCWRelativeBoundary (ActualLocalCuspCentralOrbitQuotient W) 1 = 0
  exact T.relativeBoundary_eq_zero_of_attachingDegree_eq_zero _ 1
    (constructedA2TwoCell_attachingDegree_zero W T)

public theorem constructedCellAtlas_d_three
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
    (constructedCentralCellAtlas W).skeletalComplex.d 3 2 = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  change integralCWRelativeBoundary (ActualLocalCuspCentralOrbitQuotient W) 2 = 0
  exact T.relativeBoundary_eq_zero_of_attachingDegree_eq_zero _ 2
    (constructedA2ThreeCell_attachingDegree_zero W T)

public theorem phaseSweepCellAtlas_closedImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : cuspWCellIndex n) :
    (constructedCentralCellAtlas W).cellMap n i '' Metric.closedBall 0 1 =
      (phaseSweepCellAtlas W).cellMap n i '' Metric.closedBall 0 1 :=
  (phaseSweepCellMap_closedImage W n i).symm

public theorem phaseSweepCellAtlas_d_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
    (phaseSweepCellAtlas W).skeletalComplex.d 2 1 = 0 :=
  rechartSkeletal_d_zero T _ _ (phaseSweepCellAtlas_closedImage W) 2 1
    (constructedCellAtlas_d_two W T)

public theorem phaseSweepCellAtlas_d_three
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
    (phaseSweepCellAtlas W).skeletalComplex.d 3 2 = 0 :=
  rechartSkeletal_d_zero T _ _ (phaseSweepCellAtlas_closedImage W) 3 2
    (constructedCellAtlas_d_three W T)

public def phaseSweepHomologyTwoToRelativeEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W) ≃+
      IntegralCWRelativeCellObject (ActualLocalCuspCentralOrbitQuotient W) 2 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let K := (phaseSweepCellAtlas W).skeletalComplex
  exact (T.homologyEquiv (ActualLocalCuspCentralOrbitQuotient W) 2).symm.trans
    (homologyIsoOfAdjacentZeros K 1 (phaseSweepCellAtlas_d_three W T)
      (phaseSweepCellAtlas_d_two W T)).addCommGroupIsoToAddEquiv

public def phaseSweepHomologyTwoCellEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
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
    (T : IntegralCWCellularHomologyFoundation) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ x : (CWIntegralSingularChainComplexObj
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

public theorem phaseSweepHomologyTwoCellEquiv_of_skeletalClass
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ (x : (CWIntegralSingularChainComplexObj
      (TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 3))).homology 2)
      (i : Fin 4),
    (HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainProjection
        (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2)) 2).hom x =
        T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2 (Finsupp.single i 1) →
    phaseSweepHomologyTwoCellEquiv W T
      ((HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj
          (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 3)) 2).hom x) =
      Pi.single i 1 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  intro x i hx
  funext j
  change ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
    (phaseSweepHomologyTwoToRelativeEquiv W T _)) j = _
  rw [phaseSweepHomologyTwoToRelativeEquiv_skeletal, hx, AddEquiv.symm_apply_apply]
  change (Finsupp.single i (1 : ℤ) : Fin 4 →₀ ℤ) j = (Pi.single i (1 : ℤ) : Fin 4 → ℤ) j
  simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
