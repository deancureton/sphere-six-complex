module

public import SphereSixComplex.Topology.ConstructedA2SkeletalSweep
public import SphereSixComplex.Topology.ConstructedA2PositiveCellIncidence
public import SphereSixComplex.Topology.CylinderTopPrismGenerators

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex

public def cwBallBoundaryToSphere (n : ℕ) :
    TopCat.of (cwBallBoundarySet n) ⟶ TopCat.of (CWCharacteristicBoundarySphere n) :=
  TopCat.ofHom ⟨fun b ↦ ⟨b.1.1, b.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

end SphereSixComplex

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2CircleSweepHomotopy_threeCell_last
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : unitInterval) (b : Fin 2 → ℝ) (s : ℝ) :
    constructedA2CircleSweepHomotopy W 1
      (t, constructedA2CorrectedThreeOrbit W 0 (Fin.append b ![s])) =
      constructedA2CorrectedFourOrbit W (Fin.append b ![s, 2 * (t : ℝ) - 1]) := by
  change constructedA2CentralCompactOrbitMap W _ (constructedA2CorrectedThreeOrbit W 0 _) = _
  unfold constructedA2CorrectedThreeOrbit constructedA2CorrectedFourOrbit
  rw [constructedA2CorrectedPhaseOrbit_append, constructedA2CorrectedPhaseOrbit_append,
    constructedA2CentralCompactOrbitMap_effectivePhase]
  congr 1
  rw [← mul_assoc, mul_comm _ (constructedA2ActualBoundaryGauge _), mul_assoc]
  congr 1
  ext j
  fin_cases j <;>
    simp [constructedA2CircleSweepParameter, constructedA2CircleOnePhase,
      constructedA2CircleTwoPhase, constructedCircleBallCell]

public theorem constructedA2ThreeCell_cylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (p : unitInterval × CWCharacteristicClosedBall 2) :
    constructedA2CorrectedThreeOrbit W i (cwCharacteristicCylinderHomeomorph 2 p).1 =
      constructedA2CircleSweepHomotopy W i (p.1, constructedA2CorrectedPositiveTwoOrbit W p.2.1) := by
  rw [cwCharacteristicCylinderHomeomorph_apply]
  exact (constructedA2CircleSweepHomotopy_positiveCell W i p.1 p.2.1).symm

public theorem constructedA2FourCell_cylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : unitInterval × CWCharacteristicClosedBall 3) :
    constructedA2CorrectedFourOrbit W (cwCharacteristicCylinderHomeomorph 3 p).1 =
      constructedA2CircleSweepHomotopy W 1 (p.1, constructedA2CorrectedThreeOrbit W 0 p.2.1) := by
  let b : Fin 2 → ℝ := fun j ↦ p.2.1 j.castSucc
  have hp : p.2.1 = Fin.append b ![p.2.1 2] := by
    ext j
    fin_cases j <;> rfl
  rw [cwCharacteristicCylinderHomeomorph_apply, hp]
  have ha : Fin.append (Fin.append b ![p.2.1 2]) ![2 * (p.1 : ℝ) - 1] =
      Fin.append b ![p.2.1 2, 2 * (p.1 : ℝ) - 1] := by
    ext j
    fin_cases j <;> rfl
  rw [ha]
  exact (constructedA2CircleSweepHomotopy_threeCell_last W p.1 b (p.2.1 2)).symm

public def constructedA2PositiveAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousMap (CWCharacteristicBoundarySphere 2) (constructedCentralOneSkeleton W) where
  toFun b := ⟨constructedA2CorrectedPositiveTwoOrbit W b.1,
    constructedA2CorrectedPositiveTwoOrbit_mapsTo_oneSkeleton W b.2⟩
  continuous_toFun := ((constructedA2CorrectedPositiveTwoOrbit_continuousOn W).mono
    Metric.sphere_subset_closedBall).domRestrict.subtype_mk _

public theorem constructedA2PositiveAttachingMap_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    integralSingularHomologyMap 1 (constructedA2PositiveAttachingMap W) = 0 := by
  let e := constructedA2OneSkeletonCWHomeomorph W
  have hz := cwSquareBoundaryHomologyMap_eq_zero_of_positiveLoop
    (constructedA2PositiveCellBoundaryMap W) (constructedA2PositiveCell_positiveLoop_homology_zero W)
  ext x
  apply (integralSingularHomologyEquiv 1 e).injective
  change integralSingularHomologyMap 1 ⟨e, e.continuous⟩
    (integralSingularHomologyMap 1 (constructedA2PositiveAttachingMap W) x) = _
  have hc : integralSingularHomologyMap 1 (constructedA2PositiveCellBoundaryMap W) x =
      integralSingularHomologyMap 1 ⟨e, e.continuous⟩
        (integralSingularHomologyMap 1 (constructedA2PositiveAttachingMap W) x) := by
    change ConcreteCategory.hom
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (constructedA2PositiveAttachingMap W) ≫
          TopCat.ofHom ⟨e, e.continuous⟩)) x = _
    rw [Functor.map_comp]
    rfl
  rw [← hc]
  rw [hz]
  exact (map_zero _).symm

public def constructedA2TwoSkeletonInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (constructedA2CorrectedTwoSkeleton W) ⟶
      TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public def constructedA2ThreeSkeletonInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (constructedA2CorrectedThreeSkeleton W) ⟶
      TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public def constructedA2ThreeCharacteristicPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    CWTopologicalPairMap (cwCharacteristicBoundaryInclusion 3)
      (constructedA2TwoSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨constructedA2CorrectedThreeOrbit W i b.1,
    constructedA2CorrectedThreeOrbit_mapsTo_twoSkeleton W i b.2⟩,
    ((constructedA2CorrectedThreeOrbit_continuousOn W i).mono
      Metric.sphere_subset_closedBall).domRestrict.subtype_mk _⟩
  right := TopCat.ofHom ⟨fun b ↦ constructedA2CorrectedThreeOrbit W i b.1,
    (constructedA2CorrectedThreeOrbit_continuousOn W i).domRestrict⟩
  comm := rfl

public def constructedA2FourCharacteristicPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cwCharacteristicBoundaryInclusion 4)
      (constructedA2ThreeSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨constructedA2CorrectedFourOrbit W b.1,
    constructedA2CorrectedFourOrbit_mapsTo_threeSkeleton W b.2⟩,
    ((constructedA2CorrectedFourOrbit_continuousOn W).mono
      Metric.sphere_subset_closedBall).domRestrict.subtype_mk _⟩
  right := TopCat.ofHom ⟨fun b ↦ constructedA2CorrectedFourOrbit W b.1,
    (constructedA2CorrectedFourOrbit_continuousOn W).domRestrict⟩
  comm := rfl

public def constructedA2ThreeCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 2))
      (constructedA2TwoSkeletonInclusion W) where
  left := (cwCharacteristicCylinderPair 2).left ≫ (constructedA2ThreeCharacteristicPair W i).left
  right := (cwCharacteristicCylinderPair 2).right ≫ (constructedA2ThreeCharacteristicPair W i).right
  comm := rfl

public def constructedA2FourCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 3))
      (constructedA2ThreeSkeletonInclusion W) where
  left := (cwCharacteristicCylinderPair 3).left ≫ (constructedA2FourCharacteristicPair W).left
  right := (cwCharacteristicCylinderPair 3).right ≫ (constructedA2FourCharacteristicPair W).right
  comm := rfl

public theorem constructedA2ThreeCylinderPair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (p : unitInterval × CWCharacteristicClosedBall 2) :
    (constructedA2ThreeCylinderPair W i).right p =
      constructedA2CircleSweepHomotopy W i (p.1, constructedA2CorrectedPositiveTwoOrbit W p.2.1) :=
  constructedA2ThreeCell_cylinder W i p

public theorem constructedA2FourCylinderPair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : unitInterval × CWCharacteristicClosedBall 3) :
    (constructedA2FourCylinderPair W).right p =
      constructedA2CircleSweepHomotopy W 1 (p.1, constructedA2CorrectedThreeOrbit W 0 p.2.1) :=
  constructedA2FourCell_cylinder W p

public theorem constructedCentralCellSkeleton_subset_cwSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (n : ℕ) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    constructedCentralCellSkeleton W n ⊆
      (Topology.RelCWComplex.skeletonLT
        (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W)) (n : ℕ∞) : Set _) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  dsimp only
  intro x hx
  obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hm, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, b, hb, rfl⟩ := Set.mem_iUnion.mp hx
  apply Topology.RelCWComplex.skeletonLT_mono (m := (m : ℕ∞) + 1) (by
    exact_mod_cast (show m + 1 ≤ n by omega))
  exact Topology.CWComplex.closedCell_subset_skeletonLT m j ⟨b, hb, rfl⟩

public def constructedA2TwoSkeletonToCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    TopCat.of (constructedA2CorrectedTwoSkeleton W) ⟶
      TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 3) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact TopCat.ofHom ⟨Set.inclusion
    ((constructedA2CorrectedTwoSkeleton_subset_cellSkeleton W (by decide)).trans
      (constructedCentralCellSkeleton_subset_cwSkeleton W 3)), continuous_inclusion _⟩

public def constructedA2ThreeSkeletonToCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    TopCat.of (constructedA2CorrectedThreeSkeleton W) ⟶
      TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 4) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact TopCat.ofHom ⟨Set.inclusion
    ((constructedA2CorrectedThreeSkeleton_subset_cellSkeleton W (by decide)).trans
      (constructedCentralCellSkeleton_subset_cwSkeleton W 4)), continuous_inclusion _⟩

public theorem constructedA2ThreeCharacteristicPair_toCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (constructedA2ThreeCharacteristicPair W i).left ≫ constructedA2TwoSkeletonToCW W =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 3 i).boundaryMap := by
  rfl

public theorem constructedA2FourCharacteristicPair_toCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (constructedA2FourCharacteristicPair W).left ≫ constructedA2ThreeSkeletonToCW W =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W)
        4 (0 : Fin 1)).boundaryMap := by
  rfl

public theorem constructedA2ThreeCell_attachingDegree_zero_of_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) (i : Fin 2)
    (h : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (constructedA2ThreeCharacteristicPair W i).left) 2 = 0)
    (j : Fin 4) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 2 i j = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  have hz : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj
        (T.characteristicPair (ActualLocalCuspCentralOrbitQuotient W) 3 i).boundaryMap) 2 = 0 := by
    change HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj
        (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 3 i).boundaryMap) 2 = 0
    rw [← constructedA2ThreeCharacteristicPair_toCW W i,
      cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp, h, zero_comp]
  dsimp only
  erw [T.attachingDegree_eq_homologicalAttachingMapDegree]
  unfold IntegralCWCellularHomologyFoundation.homologicalAttachingMapDegree
  rw [hz, zero_comp]
  simp
  rfl

public theorem constructedA2FourCell_attachingDegree_zero_of_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation)
    (h : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (constructedA2FourCharacteristicPair W).left) 3 = 0)
    (j : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 3 (0 : Fin 1) j = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  have hz : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj
        (T.characteristicPair (ActualLocalCuspCentralOrbitQuotient W) 4 (0 : Fin 1)).boundaryMap) 3 = 0 := by
    change HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj
        (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W)
          4 (0 : Fin 1)).boundaryMap) 3 = 0
    rw [← constructedA2FourCharacteristicPair_toCW W,
      cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp, h, zero_comp]
  dsimp only
  erw [T.attachingDegree_eq_homologicalAttachingMapDegree]
  unfold IntegralCWCellularHomologyFoundation.homologicalAttachingMapDegree
  rw [hz, zero_comp]
  simp
  rfl

public def constructedA2PositiveBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  TopCat.Homotopy.comp (constructedA2OneSkeletalSweep W i).symm
    (TopCat.Homotopy.refl (TopCat.ofHom (constructedA2PositiveAttachingMap W)))

public theorem constructedA2PositiveBoundaryReverseSweep_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology ((constructedA2PositiveBoundaryReverseSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0 = 0 := by
  let H := constructedA2PositiveBoundaryReverseSweep W i
  let K : TopCat.Homotopy _ _ := (constructedA2OneSkeletalSweep W i).symm
  have hn := closedPrismHomology_naturality
    (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (cwIntegralSingularChainMapObj (TopCat.ofHom (constructedA2PositiveAttachingMap W)))
    (cwIntegralSingularChainMapObj (𝟙 _))
    (fun p q ↦ topologicalPrism_naturality H K
      (TopCat.ofHom (constructedA2PositiveAttachingMap W)) (𝟙 _) (by ext p; rfl)
      (AddCommGrpCat.of ℤ) p q)
  have hz : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (TopCat.ofHom (constructedA2PositiveAttachingMap W))) 1 = 0 := by
    apply AddCommGrpCat.hom_ext
    exact constructedA2PositiveAttachingMap_homology_zero W
  rw [hz, zero_comp, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  exact hn.symm

public def constructedA2PositiveNestedAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (cwBallBoundarySet 2) ⟶ TopCat.of (constructedCentralOneSkeleton W) :=
  cwBallBoundaryToSphere 2 ≫ TopCat.ofHom (constructedA2PositiveAttachingMap W)

public def constructedA2PositiveNestedBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  TopCat.Homotopy.comp (constructedA2PositiveBoundaryReverseSweep W i)
    (TopCat.Homotopy.refl (cwBallBoundaryToSphere 2))

public theorem constructedA2PositiveNestedBoundaryReverseSweep_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology ((constructedA2PositiveNestedBoundaryReverseSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0 = 0 := by
  let H := constructedA2PositiveNestedBoundaryReverseSweep W i
  let K := constructedA2PositiveBoundaryReverseSweep W i
  have hn := closedPrismHomology_naturality
    (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (cwIntegralSingularChainMapObj (cwBallBoundaryToSphere 2))
    (cwIntegralSingularChainMapObj (𝟙 _))
    (fun p q ↦ topologicalPrism_naturality H K
      (cwBallBoundaryToSphere 2) (𝟙 _) (by ext p; rfl)
      (AddCommGrpCat.of ℤ) p q)
  rw [show closedPrismHomology (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0 = 0
      from constructedA2PositiveBoundaryReverseSweep_homology_zero W i,
    comp_zero, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  exact hn.symm

public def constructedA2ThreeNestedBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  TopCat.Homotopy.comp (constructedA2TwoSkeletalSweep W 1).symm
    (TopCat.Homotopy.refl (cwBallBoundaryToSphere 3 ≫ (constructedA2ThreeCharacteristicPair W 0).left))

public theorem constructedA2ThreeNestedBoundaryReverseSweep_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (h : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (constructedA2ThreeCharacteristicPair W 0).left) 2 = 0) :
    closedPrismHomology ((constructedA2ThreeNestedBoundaryReverseSweep W).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 1 = 0 := by
  let H := constructedA2ThreeNestedBoundaryReverseSweep W
  let K : TopCat.Homotopy _ _ := (constructedA2TwoSkeletalSweep W 1).symm
  let f := cwBallBoundaryToSphere 3 ≫ (constructedA2ThreeCharacteristicPair W 0).left
  have hn := closedPrismHomology_naturality
    (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 1
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (cwIntegralSingularChainMapObj f) (cwIntegralSingularChainMapObj (𝟙 _))
    (fun p q ↦ topologicalPrism_naturality H K f (𝟙 _) (by ext p; rfl)
      (AddCommGrpCat.of ℤ) p q)
  have hz : HomologicalComplex.homologyMap (cwIntegralSingularChainMapObj f) 2 = 0 := by
    rw [show f = cwBallBoundaryToSphere 3 ≫ (constructedA2ThreeCharacteristicPair W 0).left from rfl,
      cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp, h, comp_zero]
  rw [hz, zero_comp, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  exact hn.symm

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
