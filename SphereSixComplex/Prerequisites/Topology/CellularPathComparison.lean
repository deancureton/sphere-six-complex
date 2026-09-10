module

public import SphereSixComplex.Prerequisites.Topology.CellularEdgeBoundary
public import SphereSixComplex.Prerequisites.Topology.CellularSkeletalComparison

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace SphereSixComplex

public theorem cwIntegralPathChain_map {X Y : TopCat}
    (f : X ⟶ Y) (p : TopCat.I ⟶ X) :
    cwIntegralPathChain p ≫ (cwIntegralSingularChainMapObj f).f 1 =
      cwIntegralPathChain (p ≫ f) := by
  change (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₁Equiv.symm p) ≫
    (SSet.chainComplexMap (TopCat.toSSet.map f) (AddCommGrpCat.of ℤ)).f 1 = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

public theorem cwRelativePathChain_natural {A X B Y : TopCat}
    {i : A ⟶ X} {j : B ⟶ Y} (f : CWTopologicalPairMap i j) (p : TopCat.I ⟶ X) :
    cwRelativePathChain i p ≫ (cwRelativeIntegralSingularChainMapOfPair f).f 1 =
      cwRelativePathChain j (p ≫ f.right) := by
  have h := congrArg (fun q ↦ q.f 1) (cwRelativeIntegralSingularChainProjection_natural f)
  change (cwRelativeIntegralSingularChainProjection i).f 1 ≫
      (cwRelativeIntegralSingularChainMapOfPair f).f 1 =
    (cwIntegralSingularChainMapObj f.right).f 1 ≫
      (cwRelativeIntegralSingularChainProjection j).f 1 at h
  rw [cwRelativePathChain, Category.assoc, h, ← Category.assoc, cwIntegralPathChain_map]
  rfl

public theorem cwRelativePathClass_natural {A X B Y : TopCat}
    {i : A ⟶ X} {j : B ⟶ Y} (f : CWTopologicalPairMap i j)
    (p : TopCat.I ⟶ X) (a b : A) (ha : p 0 = i a) (hb : p 1 = i b)
    (ha' : (p ≫ f.right) 0 = j (f.left a))
    (hb' : (p ≫ f.right) 1 = j (f.left b)) :
    cwRelativePathClass i p a b ha hb ≫
        HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainMapOfPair f) 1 =
      cwRelativePathClass j (p ≫ f.right) (f.left a) (f.left b) ha' hb' := by
  unfold cwRelativePathClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 1
  rw [← cancel_mono ((CWRelativeIntegralSingularChainComplex j).iCycles 1),
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact cwRelativePathChain_natural f p

public theorem cwIntegralPathDifference_cycle {X : TopCat} (p q : TopCat.I ⟶ X)
    (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) :
    (cwIntegralPathChain p - cwIntegralPathChain q) ≫
      (CWIntegralSingularChainComplexObj X).d 1 0 = 0 := by
  rw [Preadditive.sub_comp, cwIntegralPathChain_boundary, cwIntegralPathChain_boundary,
    h₀, h₁, sub_self]

public def cwIntegralPathDifferenceClass {X : TopCat} (p q : TopCat.I ⟶ X)
    (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) :
    AddCommGrpCat.of ℤ ⟶ (CWIntegralSingularChainComplexObj X).homology 1 :=
  (CWIntegralSingularChainComplexObj X).liftCycles
      (cwIntegralPathChain p - cwIntegralPathChain q) 0 (by simp)
      (cwIntegralPathDifference_cycle p q h₀ h₁) ≫
    (CWIntegralSingularChainComplexObj X).homologyπ 1

public theorem cwIntegralPathDifferenceClass_relative {A X : TopCat} (i : A ⟶ X)
    (p q : TopCat.I ⟶ X) (a b : A)
    (hp₀ : p 0 = i a) (hp₁ : p 1 = i b)
    (hq₀ : q 0 = i a) (hq₁ : q 1 = i b) :
    cwIntegralPathDifferenceClass p q (hp₀.trans hq₀.symm) (hp₁.trans hq₁.symm) ≫
        HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection i) 1 =
      cwRelativePathClass i p a b hp₀ hp₁ - cwRelativePathClass i q a b hq₀ hq₁ := by
  unfold cwIntegralPathDifferenceClass cwRelativePathClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap,
    ← Preadditive.sub_comp]
  congr 1
  rw [← cancel_mono ((CWRelativeIntegralSingularChainComplex i).iCycles 1)]
  simp only [Preadditive.sub_comp, HomologicalComplex.liftCycles_i, cwRelativePathChain]

public theorem normalized_cellBasis_single_one
    (T : IntegralCWCellularHomologyFoundation) (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    T.normalized.cellBasis X 1 (Finsupp.single e 1) =
      (cwRelativePathClass (integralCWSkeletonInclusion X 1)
        (cwOrientedIntervalPath ≫ (integralCWCharacteristicPairMap X 1 e).diskMap)
        ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft)
        ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight)
        (by
          change (integralCWCharacteristicPairMap X 1 e).diskMap (cwOrientedIntervalPath 0) = _
          rw [cwOrientedIntervalPath_left]
          exact ConcreteCategory.congr_hom (integralCWCharacteristicPairMap X 1 e).comm _)
        (by
          change (integralCWCharacteristicPairMap X 1 e).diskMap (cwOrientedIntervalPath 1) = _
          rw [cwOrientedIntervalPath_right]
          exact ConcreteCategory.congr_hom (integralCWCharacteristicPairMap X 1 e).comm _)).hom 1 := by
  rw [T.normalized.cellBasis_single, T.normalized_diskOrientation_one,
    normalizedIntervalDiskOrientation_symm_one]
  exact ConcreteCategory.congr_hom
    (cwRelativePathClass_natural
      ⟨(integralCWCharacteristicPairMap X 1 e).boundaryMap,
        (integralCWCharacteristicPairMap X 1 e).diskMap,
        (integralCWCharacteristicPairMap X 1 e).comm⟩
      cwOrientedIntervalPath cwBoundaryOneLeft cwBoundaryOneRight
      cwOrientedIntervalPath_left cwOrientedIntervalPath_right _ _) 1

public def cwCellularEdgePath (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    TopCat.I ⟶ TopCat.of (IntegralCWSkeletonLT X 2) :=
  cwOrientedIntervalPath ≫ (integralCWCharacteristicPairMap X 1 e).diskMap

public theorem cwCellularEdgePath_left (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    cwCellularEdgePath X e 0 = integralCWSkeletonInclusion X 1
      ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft) := by
  change (integralCWCharacteristicPairMap X 1 e).diskMap (cwOrientedIntervalPath 0) = _
  rw [cwOrientedIntervalPath_left]
  exact ConcreteCategory.congr_hom (integralCWCharacteristicPairMap X 1 e).comm _

public theorem cwCellularEdgePath_right (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    cwCellularEdgePath X e 1 = integralCWSkeletonInclusion X 1
      ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight) := by
  change (integralCWCharacteristicPairMap X 1 e).diskMap (cwOrientedIntervalPath 1) = _
  rw [cwOrientedIntervalPath_right]
  exact ConcreteCategory.congr_hom (integralCWCharacteristicPairMap X 1 e).comm _

public theorem normalized_cellBasis_edgeDifference
    (T : IntegralCWCellularHomologyFoundation) (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e f : Topology.CWComplex.cell (Set.univ : Set X) 1)
    (h₀ : (integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft =
      (integralCWCharacteristicPairMap X 1 f).boundaryMap cwBoundaryOneLeft)
    (h₁ : (integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight =
      (integralCWCharacteristicPairMap X 1 f).boundaryMap cwBoundaryOneRight) :
    (T.normalized.cellBasis X 1).symm
      ((cwIntegralPathDifferenceClass (cwCellularEdgePath X e) (cwCellularEdgePath X f)
          ((cwCellularEdgePath_left X e).trans
            ((congrArg (integralCWSkeletonInclusion X 1) h₀).trans
              (cwCellularEdgePath_left X f).symm))
          ((cwCellularEdgePath_right X e).trans
            ((congrArg (integralCWSkeletonInclusion X 1) h₁).trans
              (cwCellularEdgePath_right X f).symm)) ≫
        HomologicalComplex.homologyMap
          (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X 1)) 1).hom 1) =
      Finsupp.single e 1 - Finsupp.single f 1 := by
  have he := cwIntegralPathDifferenceClass_relative (integralCWSkeletonInclusion X 1)
    (cwCellularEdgePath X e) (cwCellularEdgePath X f)
    ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft)
    ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight)
    (cwCellularEdgePath_left X e) (cwCellularEdgePath_right X e)
    ((cwCellularEdgePath_left X f).trans (congrArg (integralCWSkeletonInclusion X 1) h₀.symm))
    ((cwCellularEdgePath_right X f).trans (congrArg (integralCWSkeletonInclusion X 1) h₁.symm))
  have hf : cwRelativePathClass (integralCWSkeletonInclusion X 1) (cwCellularEdgePath X f)
      ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft)
      ((integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight)
      ((cwCellularEdgePath_left X f).trans
        (congrArg (integralCWSkeletonInclusion X 1) h₀.symm))
      ((cwCellularEdgePath_right X f).trans
        (congrArg (integralCWSkeletonInclusion X 1) h₁.symm)) =
    cwRelativePathClass (integralCWSkeletonInclusion X 1) (cwCellularEdgePath X f)
      ((integralCWCharacteristicPairMap X 1 f).boundaryMap cwBoundaryOneLeft)
      ((integralCWCharacteristicPairMap X 1 f).boundaryMap cwBoundaryOneRight)
      (cwCellularEdgePath_left X f) (cwCellularEdgePath_right X f) := by
    congr 1
  have hev := congrArg (fun k ↦ k.hom 1) he
  rw [hf] at hev
  simp only [AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply] at hev
  dsimp only [cwCellularEdgePath] at hev
  rw [← normalized_cellBasis_single_one T X e,
    ← normalized_cellBasis_single_one T X f] at hev
  dsimp only [cwCellularEdgePath]
  rw [hev, ← map_sub, AddEquiv.symm_apply_apply]

end SphereSixComplex
