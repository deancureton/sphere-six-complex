module

public import SphereSixComplex.Topology.CellularNormalizedFoundation

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SphereSixComplex

public theorem cwIntegralPointClass_natural {A X : TopCat} (i : A ⟶ X) (a : A) :
    cwIntegralPointClass A a ≫ HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj i) 0 = cwIntegralPointClass X (i a) := by
  unfold cwIntegralPointClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  rw [cwIntegralPointChain_map]

public def cwSkeletalPointClass (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (p : IntegralCWSkeletonLT X 1) :
    AddCommGrpCat.of ℤ ⟶ IntegralCWRelativeCellObject X 0 :=
  cwIntegralPointClass (TopCat.of (IntegralCWSkeletonLT X 1)) p ≫
    HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection
      (integralCWSkeletonInclusion X 0)) 0

public theorem normalized_cellBasis_single_zero
    (T : IntegralCWCellularHomologyFoundation) (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    T.normalized.cellBasis X 0 (Finsupp.single e 1) =
      (cwSkeletalPointClass X ((integralCWCharacteristicPairMap X 0 e).diskMap cwPointDiskPoint)).hom 1 := by
  rw [T.normalized.cellBasis_single, T.normalized_diskOrientation_zero,
    normalizedPointDiskOrientation_symm_one]
  have h := cwRelativeIntegralSingularChainProjection_natural
    (show CWTopologicalPairMap (cwCharacteristicBoundaryInclusion 0)
      (integralCWSkeletonInclusion X 0) from
      ⟨(integralCWCharacteristicPairMap X 0 e).boundaryMap,
        (integralCWCharacteristicPairMap X 0 e).diskMap,
        (integralCWCharacteristicPairMap X 0 e).comm⟩)
  have hh := congrArg (fun f ↦ HomologicalComplex.homologyMap f 0) h
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
  have he := congrArg (fun f ↦ cwIntegralPointClass
    (TopCat.of (CWCharacteristicClosedBall 0)) cwPointDiskPoint ≫ f) hh
  simp only [← Category.assoc] at he
  rw [cwIntegralPointClass_natural] at he
  exact ConcreteCategory.congr_hom he 1

public theorem normalized_cellBasis_single_one_boundary
    (T : IntegralCWCellularHomologyFoundation) (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    (integralCWRelativeBoundary X 0).hom (T.normalized.cellBasis X 1 (Finsupp.single e 1)) =
      (cwSkeletalPointClass X ((integralCWCharacteristicPairMap X 1 e).boundaryMap
        cwBoundaryOneRight)).hom 1 -
      (cwSkeletalPointClass X ((integralCWCharacteristicPairMap X 1 e).boundaryMap
        cwBoundaryOneLeft)).hom 1 := by
  rw [T.normalized.cellBasis_single, T.normalized_diskOrientation_one,
    normalizedIntervalDiskOrientation_symm_one]
  have h := congrArg (fun f ↦ cwOrientedIntervalClass ≫ f ≫
    HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection
      (integralCWSkeletonInclusion X 0)) 0) (integralCWCharacteristicBoundary_natural X 0 e).symm
  have hb : cwOrientedIntervalClass ≫
      cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 1) 0 =
      cwIntegralPointClass (TopCat.of (CWCharacteristicBoundarySphere 1)) cwBoundaryOneRight -
      cwIntegralPointClass (TopCat.of (CWCharacteristicBoundarySphere 1)) cwBoundaryOneLeft :=
    cwRelativePathClass_boundary_pointClasses (cwCharacteristicBoundaryInclusion 1)
      cwOrientedIntervalPath cwBoundaryOneLeft cwBoundaryOneRight
      cwOrientedIntervalPath_left cwOrientedIntervalPath_right
  simp only [← Category.assoc] at h
  rw [hb, Preadditive.sub_comp, cwIntegralPointClass_natural,
    cwIntegralPointClass_natural, Preadditive.sub_comp] at h
  exact ConcreteCategory.congr_hom h 1

public theorem normalized_cellular_edge_boundary
    (T : IntegralCWCellularHomologyFoundation) (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 1)
    (a b : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (ha : (integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft =
      (integralCWCharacteristicPairMap X 0 a).diskMap cwPointDiskPoint)
    (hb : (integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight =
      (integralCWCharacteristicPairMap X 0 b).diskMap cwPointDiskPoint) :
    (T.normalized.cellBasis X 0).symm
      ((integralCWRelativeBoundary X 0).hom
        (T.normalized.cellBasis X 1 (Finsupp.single e 1))) =
      Finsupp.single b 1 - Finsupp.single a 1 := by
  rw [normalized_cellBasis_single_one_boundary, ha, hb,
    ← normalized_cellBasis_single_zero T X a, ← normalized_cellBasis_single_zero T X b,
    ← map_sub, AddEquiv.symm_apply_apply]

end SphereSixComplex
