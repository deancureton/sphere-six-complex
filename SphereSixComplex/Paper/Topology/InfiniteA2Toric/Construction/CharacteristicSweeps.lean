module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.SkeletalSweep
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveCellIncidence
public import SphereSixComplex.Prerequisites.Topology.CylinderTopPrismGenerators

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex

public def cwBallBoundaryToSphere (n : ℕ) :
    TopCat.of (cwBallBoundarySet n) ⟶ TopCat.of (CWCharacteristicBoundarySphere n) :=
  TopCat.ofHom ⟨fun b ↦ ⟨b.1.1, b.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

end SphereSixComplex

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem circleSweepHomotopy_threeCell_last
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : unitInterval) (b : Fin 2 → ℝ) (s : ℝ) :
    circleSweepHomotopy W 1
      (t, correctedThreeOrbit W 0 (Fin.append b ![s])) =
      correctedFourOrbit W (Fin.append b ![s, 2 * (t : ℝ) - 1]) := by
  change centralCompactOrbitMap W _ (correctedThreeOrbit W 0 _) = _
  unfold correctedThreeOrbit correctedFourOrbit
  rw [correctedPhaseOrbit_append, correctedPhaseOrbit_append,
    centralCompactOrbitMap_effectivePhase]
  congr 1
  rw [← mul_assoc, mul_comm _ (actualBoundaryGauge _), mul_assoc]
  congr 1
  ext j
  fin_cases j <;>
    simp [circleSweepParameter, CircleCell.onePhase,
      CircleCell.twoPhase, CircleCell.ballParam]

public theorem threeCell_cylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (p : unitInterval × CWCharacteristicClosedBall 2) :
    correctedThreeOrbit W i (cwCharacteristicCylinderHomeomorph 2 p).1 =
      circleSweepHomotopy W i (p.1, correctedPositiveTwoOrbit W p.2.1) := by
  rw [cwCharacteristicCylinderHomeomorph_apply]
  exact (circleSweepHomotopy_positiveCell W i p.1 p.2.1).symm

public theorem fourCell_cylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : unitInterval × CWCharacteristicClosedBall 3) :
    correctedFourOrbit W (cwCharacteristicCylinderHomeomorph 3 p).1 =
      circleSweepHomotopy W 1 (p.1, correctedThreeOrbit W 0 p.2.1) := by
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
  exact (circleSweepHomotopy_threeCell_last W p.1 b (p.2.1 2)).symm

public def positiveAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousMap (CWCharacteristicBoundarySphere 2) (constructedCentralOneSkeleton W) where
  toFun b := ⟨correctedPositiveTwoOrbit W b.1,
    correctedPositiveTwoOrbit_mapsTo_oneSkeleton W b.2⟩
  continuous_toFun := ((continuousOn_correctedPositiveTwoOrbit W).mono
    Metric.sphere_subset_closedBall).domRestrict.subtype_mk _

public theorem positiveAttachingMap_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    integralSingularHomologyMap 1 (positiveAttachingMap W) = 0 := by
  let e := oneSkeletonCWHomeomorph W
  have hz := cwSquareBoundaryHomologyMap_eq_zero_of_positiveLoop
    (positiveCellBoundaryMap W) (positiveCell_positiveLoop_homology_zero W)
  ext x
  apply (integralSingularHomologyEquiv 1 e).injective
  change integralSingularHomologyMap 1 ⟨e, e.continuous⟩
    (integralSingularHomologyMap 1 (positiveAttachingMap W) x) = _
  have hc : integralSingularHomologyMap 1 (positiveCellBoundaryMap W) x =
      integralSingularHomologyMap 1 ⟨e, e.continuous⟩
        (integralSingularHomologyMap 1 (positiveAttachingMap W) x) := by
    change ConcreteCategory.hom
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (positiveAttachingMap W) ≫
          TopCat.ofHom ⟨e, e.continuous⟩)) x = _
    rw [Functor.map_comp]
    rfl
  rw [← hc]
  rw [hz]
  exact (map_zero _).symm

public def twoSkeletonInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (correctedTwoSkeleton W) ⟶
      TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public def threeSkeletonInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (correctedThreeSkeleton W) ⟶
      TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public def threeCharacteristicPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    CWTopologicalPairMap (cwCharacteristicBoundaryInclusion 3)
      (twoSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨correctedThreeOrbit W i b.1,
    correctedThreeOrbit_mapsTo_twoSkeleton W i b.2⟩,
    ((continuousOn_correctedThreeOrbit W i).mono
      Metric.sphere_subset_closedBall).domRestrict.subtype_mk _⟩
  right := TopCat.ofHom ⟨fun b ↦ correctedThreeOrbit W i b.1,
    (continuousOn_correctedThreeOrbit W i).domRestrict⟩
  comm := rfl

public def fourCharacteristicPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cwCharacteristicBoundaryInclusion 4)
      (threeSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨correctedFourOrbit W b.1,
    correctedFourOrbit_mapsTo_threeSkeleton W b.2⟩,
    ((continuousOn_correctedFourOrbit W).mono
      Metric.sphere_subset_closedBall).domRestrict.subtype_mk _⟩
  right := TopCat.ofHom ⟨fun b ↦ correctedFourOrbit W b.1,
    (continuousOn_correctedFourOrbit W).domRestrict⟩
  comm := rfl

public def threeCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 2))
      (twoSkeletonInclusion W) where
  left := (cwCharacteristicCylinderPair 2).left ≫ (threeCharacteristicPair W i).left
  right := (cwCharacteristicCylinderPair 2).right ≫ (threeCharacteristicPair W i).right
  comm := rfl

public def fourCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 3))
      (threeSkeletonInclusion W) where
  left := (cwCharacteristicCylinderPair 3).left ≫ (fourCharacteristicPair W).left
  right := (cwCharacteristicCylinderPair 3).right ≫ (fourCharacteristicPair W).right
  comm := rfl

public theorem threeCylinderPair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (p : unitInterval × CWCharacteristicClosedBall 2) :
    (threeCylinderPair W i).right p =
      circleSweepHomotopy W i (p.1, correctedPositiveTwoOrbit W p.2.1) :=
  threeCell_cylinder W i p

public theorem fourCylinderPair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : unitInterval × CWCharacteristicClosedBall 3) :
    (fourCylinderPair W).right p =
      circleSweepHomotopy W 1 (p.1, correctedThreeOrbit W 0 p.2.1) :=
  fourCell_cylinder W p

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

public def twoSkeletonToCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    TopCat.of (correctedTwoSkeleton W) ⟶
      TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 3) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact TopCat.ofHom ⟨Set.inclusion
    ((constructedA2CorrectedTwoSkeleton_subset_cellSkeleton W (by decide)).trans
      (constructedCentralCellSkeleton_subset_cwSkeleton W 3)), continuous_inclusion _⟩

public def threeSkeletonToCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    TopCat.of (correctedThreeSkeleton W) ⟶
      TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 4) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact TopCat.ofHom ⟨Set.inclusion
    ((constructedA2CorrectedThreeSkeleton_subset_cellSkeleton W (by decide)).trans
      (constructedCentralCellSkeleton_subset_cwSkeleton W 4)), continuous_inclusion _⟩

public theorem threeCharacteristicPair_toCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (threeCharacteristicPair W i).left ≫ twoSkeletonToCW W =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 3 i).boundaryMap := by
  rfl

public theorem fourCharacteristicPair_toCW
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (fourCharacteristicPair W).left ≫ threeSkeletonToCW W =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W)
        4 (0 : Fin 1)).boundaryMap := by
  rfl

public theorem threeCell_attachingDegree_zero_of_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 2)
    (h : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (threeCharacteristicPair W i).left) 2 = 0)
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
    rw [← threeCharacteristicPair_toCW W i,
      cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp, h, zero_comp]
  dsimp only
  erw [T.attachingDegree_eq_homologicalAttachingMapDegree]
  unfold CellularHomology.IntegralComparison.homologicalAttachingMapDegree
  rw [hz, zero_comp]
  simp
  rfl

public theorem fourCell_attachingDegree_zero_of_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison)
    (h : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (fourCharacteristicPair W).left) 3 = 0)
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
    rw [← fourCharacteristicPair_toCW W,
      cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp, h, zero_comp]
  dsimp only
  erw [T.attachingDegree_eq_homologicalAttachingMapDegree]
  unfold CellularHomology.IntegralComparison.homologicalAttachingMapDegree
  rw [hz, zero_comp]
  simp
  rfl

public def positiveBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  TopCat.Homotopy.comp (oneSkeletalSweep W i).symm
    (TopCat.Homotopy.refl (TopCat.ofHom (positiveAttachingMap W)))

public theorem positiveBoundaryReverseSweep_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology ((positiveBoundaryReverseSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0 = 0 := by
  let H := positiveBoundaryReverseSweep W i
  let K : TopCat.Homotopy _ _ := (oneSkeletalSweep W i).symm
  have hn := closedPrismHomology_naturality
    (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (cwIntegralSingularChainMapObj (TopCat.ofHom (positiveAttachingMap W)))
    (cwIntegralSingularChainMapObj (𝟙 _))
    (fun p q ↦ topologicalPrism_naturality H K
      (TopCat.ofHom (positiveAttachingMap W)) (𝟙 _) (by ext p; rfl)
      (AddCommGrpCat.of ℤ) p q)
  have hz : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (TopCat.ofHom (positiveAttachingMap W))) 1 = 0 := by
    apply AddCommGrpCat.hom_ext
    exact positiveAttachingMap_homology_zero W
  rw [hz, zero_comp, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  exact hn.symm


public def positiveNestedBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  TopCat.Homotopy.comp (positiveBoundaryReverseSweep W i)
    (TopCat.Homotopy.refl (cwBallBoundaryToSphere 2))

public theorem positiveNestedBoundaryReverseSweep_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology ((positiveNestedBoundaryReverseSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0 = 0 := by
  let H := positiveNestedBoundaryReverseSweep W i
  let K := positiveBoundaryReverseSweep W i
  have hn := closedPrismHomology_naturality
    (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (cwIntegralSingularChainMapObj (cwBallBoundaryToSphere 2))
    (cwIntegralSingularChainMapObj (𝟙 _))
    (fun p q ↦ topologicalPrism_naturality H K
      (cwBallBoundaryToSphere 2) (𝟙 _) (by ext p; rfl)
      (AddCommGrpCat.of ℤ) p q)
  rw [show closedPrismHomology (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 0 = 0
      from positiveBoundaryReverseSweep_homology_zero W i,
    comp_zero, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  exact hn.symm

public def threeNestedBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  TopCat.Homotopy.comp (twoSkeletalSweep W 1).symm
    (TopCat.Homotopy.refl (cwBallBoundaryToSphere 3 ≫ (threeCharacteristicPair W 0).left))

public theorem threeNestedBoundaryReverseSweep_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (h : HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (threeCharacteristicPair W 0).left) 2 = 0) :
    closedPrismHomology ((threeNestedBoundaryReverseSweep W).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 1 = 0 := by
  let H := threeNestedBoundaryReverseSweep W
  let K : TopCat.Homotopy _ _ := (twoSkeletalSweep W 1).symm
  let f := cwBallBoundaryToSphere 3 ≫ (threeCharacteristicPair W 0).left
  have hn := closedPrismHomology_naturality
    (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) 1
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
    (cwIntegralSingularChainMapObj f) (cwIntegralSingularChainMapObj (𝟙 _))
    (fun p q ↦ topologicalPrism_naturality H K f (𝟙 _) (by ext p; rfl)
      (AddCommGrpCat.of ℤ) p q)
  have hz : HomologicalComplex.homologyMap (cwIntegralSingularChainMapObj f) 2 = 0 := by
    rw [show f = cwBallBoundaryToSphere 3 ≫ (threeCharacteristicPair W 0).left from rfl,
      cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp, h, comp_zero]
  rw [hz, zero_comp, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  exact hn.symm

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
