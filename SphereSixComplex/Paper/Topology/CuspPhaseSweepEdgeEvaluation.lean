module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepEdgeComparison
public import SphereSixComplex.Prerequisites.Topology.CylinderTimeReflection

@[expose] public section
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits HomologicalComplex Matrix MonoidalCategory
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction CuspFilling CuspPeriodExpansion
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

theorem circleSweepParameter_eq_period (i : Fin 2) (t : unitInterval) :
    constructedA2CircleSweepParameter i t = cuspPeriodCompactCircle i ((t : ℝ) : UnitAddCircle) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [constructedA2CircleSweepParameter, constructedA2CircleOnePhase,
      CircleCell.ballParam, CircleCell.param, cuspPeriodCompactCircle,
      AddCircle.toCircle_apply_mk]
  all_goals congr 2; ring


def phaseSweepForwardCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 1))
      (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact if i = 0 then
    { left := (cylinderTimeReflectionPair (cwBallBoundarySet 1)).left ≫
        (phaseSweepCylinderPair W i).left
      right := (cylinderTimeReflectionPair (cwBallBoundarySet 1)).right ≫
        (phaseSweepCylinderPair W i).right
      comm := by
        rw [← Category.assoc, (cylinderTimeReflectionPair (cwBallBoundarySet 1)).comm,
          Category.assoc, (phaseSweepCylinderPair W i).comm, Category.assoc] }
    else phaseSweepCylinderPair W i

theorem negate_complement_addCircle (t : ℝ) :
    (-((1 - t : ℝ) : UnitAddCircle)) = (t : UnitAddCircle) := by
  have h1 : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period 1
  rw [AddCircle.coe_sub, h1, zero_sub, neg_neg]

theorem phaseSweepForwardCylinderPair_reverse
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3)
    (p : unitInterval × CWCharacteristicClosedBall 1) :
    (phaseSweepSkeletalHomotopy W (phaseSweepPeriod i))
      (p.1, (phaseSweepEdgeBasePair W i).right p.2) =
      cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 1))
        (phaseSweepForwardCylinderPair W i).right p := by
  apply Subtype.ext
  change constructedA2CentralCompactOrbitMap W (constructedA2CircleSweepParameter
    (phaseSweepPeriod i) p.1) ((phaseSweepEdgeBasePair W i).right p.2).1 = _
  rw [circleSweepParameter_eq_period, phaseSweepEdgeBasePair_apply]
  have hb : p.2.1 = (fun _ ↦ p.2.1 0) := by ext j; fin_cases j; rfl
  rw [hb]
  have ht : cylinderVerticalScale p.1 1 = unitInterval.symm p.1 := by
    apply Subtype.ext
    simp [cylinderVerticalScale, unitInterval.symm]
  change _ = ((phaseSweepForwardCylinderPair W i).right
    (cylinderVerticalScale p.1 1, p.2)).1
  rw [ht]
  fin_cases i
  · change _ = ((phaseSweepCylinderPair W 0).right
      (unitInterval.symm (unitInterval.symm p.1), p.2)).1
    rw [unitInterval.symm_symm, phaseSweepCylinderPair_apply, phaseSweepOrbit_period]
    rfl
  · change _ = ((phaseSweepCylinderPair W 1).right (unitInterval.symm p.1, p.2)).1
    rw [phaseSweepCylinderPair_apply, phaseSweepOrbit_period]
    change _ = constructedA2CentralCompactOrbitMap W
      (cuspPeriodCompactCircle 0 (-((1 - (p.1 : ℝ) : ℝ) : UnitAddCircle))) _
    rw [negate_complement_addCircle]
    rfl
  · change _ = ((phaseSweepCylinderPair W 2).right (unitInterval.symm p.1, p.2)).1
    rw [phaseSweepCylinderPair_apply, phaseSweepOrbit_period]
    change _ = constructedA2CentralCompactOrbitMap W
      (cuspPeriodCompactCircle 1 (-((1 - (p.1 : ℝ) : ℝ) : UnitAddCircle))) _
    rw [negate_complement_addCircle]
    rfl

theorem phaseSweepRelativePrism_edge
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W (phaseSweepPeriod i)) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single i 1)) =
        homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepForwardCylinderPair W i)) 2
          orientedIntervalCylinderPrism := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  let : Mono (cylinderBaseInclusion (cwBallBoundarySet 1)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  have hc := cylinderRelativePrism_to_relativeHomotopy
    (X := TopCat.of (CWCharacteristicClosedBall 1)) (cwBallBoundarySet 1)
    (phaseSweepForwardCylinderPair W i) (phaseSweepEdgeBasePair W i)
    (phaseSweepSkeletalBasePair W)
    (TopCat.Homotopy.refl (phaseSweepSkeletalBasePair W).left)
    (phaseSweepSkeletalHomotopy W (phaseSweepPeriod i)) (by
      ext p : 1
      apply Subtype.ext
      exact phaseSweepCompactAction_zeroSkeleton W
        (constructedA2CircleSweepParameter (phaseSweepPeriod i) p.2.down) p.1)
    (by
      ext p : 1
      exact phaseSweepForwardCylinderPair_reverse W i (p.2.down, p.1)) 0
  have hh := ConcreteCategory.congr_hom hc
    (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 (cwOrientedIntervalClass.hom 1))
  change closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W (phaseSweepPeriod i)) 0
    (homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepEdgeBasePair W i)) 1
      (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 (cwOrientedIntervalClass.hom 1))) = _ at hh
  rw [phaseSweepEdgeBasePair_orientedClass T W i] at hh
  rw [← cylinderTopPrismHomologyIso_map_pair] at hh
  exact hh

theorem phaseSweepRelativePrism_edge_unit
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∃ u : ℤ, (u = 1 ∨ u = -1) ∧
      closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W (phaseSweepPeriod i)) 0
        (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single i 1)) =
          u • T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2
            (Finsupp.single (phaseSweepCellIndex i) 1) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  obtain ⟨u, hu, h⟩ := phaseSweepOrientedPrism_images (N := N) T
  rw [phaseSweepRelativePrism_edge]
  by_cases hi : i = 0
  · subst i
    have hc : cwRelativeIntegralSingularChainMapOfPair (phaseSweepForwardCylinderPair W 0) =
        cwRelativeIntegralSingularChainMapOfPair (cylinderTimeReflectionPair (cwBallBoundarySet 1)) ≫
          cwRelativeIntegralSingularChainMapOfPair (phaseSweepCylinderPair W 0) :=
      cwRelativeIntegralSingularChainMapOfPair_comp _ _
    rw [hc, homologyMap_comp]
    change ∃ v, (v = 1 ∨ v = -1) ∧
      homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepCylinderPair W 0)) 2
        (homologyMap (cwRelativeIntegralSingularChainMapOfPair
          (cylinderTimeReflectionPair (cwBallBoundarySet 1))) 2 orientedIntervalCylinderPrism) = _
    rcases cylinderTimeReflection_orientedIntervalPrism T with hr | hr
    · refine ⟨u, hu, ?_⟩
      rw [hr]
      exact h W 0
    · refine ⟨-u, ?_, ?_⟩
      · rcases hu with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · rw [hr, map_neg, h W 0]
        exact (neg_zsmul _ _).symm
  · refine ⟨u, hu, ?_⟩
    have hf : phaseSweepForwardCylinderPair W i = phaseSweepCylinderPair W i := by
      simp only [phaseSweepForwardCylinderPair, hi, ↓reduceIte]
    rw [hf]
    exact h W i

theorem phaseSweepRelativePrism_edge_of_cylinder
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) (j : Fin 2) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ (F : CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 1))
      (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2)),
      (∀ p : unitInterval × CWCharacteristicClosedBall 1,
        phaseSweepSkeletalHomotopy W j (p.1, (phaseSweepEdgeBasePair W i).right p.2) =
          cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 1)) F.right p) →
    closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W j) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single i 1)) =
        homologyMap (cwRelativeIntegralSingularChainMapOfPair F) 2
          orientedIntervalCylinderPrism := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  intro F hF
  let : Mono (cylinderBaseInclusion (cwBallBoundarySet 1)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  have hc := cylinderRelativePrism_to_relativeHomotopy
    (X := TopCat.of (CWCharacteristicClosedBall 1)) (cwBallBoundarySet 1)
    F (phaseSweepEdgeBasePair W i)
    (phaseSweepSkeletalBasePair W)
    (TopCat.Homotopy.refl (phaseSweepSkeletalBasePair W).left)
    (phaseSweepSkeletalHomotopy W j) (by
      ext p : 1
      apply Subtype.ext
      exact phaseSweepCompactAction_zeroSkeleton W
        (constructedA2CircleSweepParameter j p.2.down) p.1)
    (by
      ext p : 1
      exact hF (p.2.down, p.1)) 0
  have hh := ConcreteCategory.congr_hom hc
    (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 (cwOrientedIntervalClass.hom 1))
  change closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W j) 0
    (homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepEdgeBasePair W i)) 1
      (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 (cwOrientedIntervalClass.hom 1))) = _ at hh
  rw [phaseSweepEdgeBasePair_orientedClass T W i] at hh
  rw [← cylinderTopPrismHomologyIso_map_pair] at hh
  exact hh

def phaseSweepFixedCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 1))
      (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact
    { left := TopCat.ofHom ⟨fun p ↦ (phaseSweepEdgeBasePair W i).right p.1.2, by fun_prop⟩
      right := TopCat.ofHom ⟨fun p ↦ (phaseSweepOneSkeletonInclusion W)
        ((phaseSweepEdgeBasePair W i).right p.2), by fun_prop⟩
      comm := rfl }

theorem phaseSweepFixedCylinderPair_chainMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    cwRelativeIntegralSingularChainMapOfPair (phaseSweepFixedCylinderPair W i) = 0 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let v : TopCat.of (unitInterval × CWCharacteristicClosedBall 1) ⟶
      TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) :=
    TopCat.ofHom ⟨fun p ↦ (phaseSweepEdgeBasePair W i).right p.2, by fun_prop⟩
  have hv : (phaseSweepFixedCylinderPair W i).right = v ≫
      integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2 := rfl
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel
    (cwIntegralSingularChainMapObj (cylinderBoundaryInclusion (cwBallBoundarySet 1))))
  change cwRelativeIntegralSingularChainProjection _ ≫ _ =
    cwRelativeIntegralSingularChainProjection _ ≫ _
  rw [cwRelativeIntegralSingularChainProjection_natural, hv,
    cwIntegralSingularChainMapObj_comp, Category.assoc, comp_zero]
  have hz := (cwRelativeIntegralSingularShortComplex
    (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2)).zero
  change cwIntegralSingularChainMapObj v ≫
    (cwRelativeIntegralSingularShortComplex _).f ≫ (cwRelativeIntegralSingularShortComplex _).g = 0
  erw [hz, comp_zero]

theorem phaseSweepRelativePrism_fixed_edge
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j : Fin 2) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    let i : Fin 3 := if j = 0 then 2 else 1
    closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W j) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single i 1)) = 0 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  let i : Fin 3 := if j = 0 then 2 else 1
  have hp : ∀ p : unitInterval × CWCharacteristicClosedBall 1,
      phaseSweepSkeletalHomotopy W j (p.1, (phaseSweepEdgeBasePair W i).right p.2) =
        cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 1))
          (phaseSweepFixedCylinderPair W i).right p := by
    intro p
    apply Subtype.ext
    change constructedA2CentralCompactOrbitMap W (constructedA2CircleSweepParameter j p.1)
      ((phaseSweepEdgeBasePair W i).right p.2).1 = _
    rw [circleSweepParameter_eq_period, phaseSweepEdgeBasePair_apply]
    change constructedA2CentralCompactOrbitMap W (cuspPeriodCompactCircle j ((p.1 : ℝ) : UnitAddCircle))
      (constructedCentralOneCell W i p.2.1) = constructedCentralOneCell W i p.2.1
    fin_cases j
    · exact compactOrbit_eq_self_of_carrier W 2 0 _ _ (thirdPhase_edgeTwo_fixed _ _)
    · exact compactOrbit_eq_self_of_carrier W 1 1 _ _ (fourthPhase_edgeOne_fixed _ _)
  rw [phaseSweepRelativePrism_edge_of_cylinder T W i j (phaseSweepFixedCylinderPair W i) hp,
    phaseSweepFixedCylinderPair_chainMap, homologyMap_zero]
  rfl

theorem phaseSweepRelativePrism_edgeZero_equal
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (phaseSweepCellAtlas W).cwComplex
    closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W 1) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single (0 : Fin 3) 1)) =
    closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W 0) 0
      (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1 (Finsupp.single (0 : Fin 3) 1)) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  have hp : ∀ p : unitInterval × CWCharacteristicClosedBall 1,
      phaseSweepSkeletalHomotopy W 1 (p.1, (phaseSweepEdgeBasePair W 0).right p.2) =
        cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 1))
          (phaseSweepForwardCylinderPair W 0).right p := by
    intro p
    calc
      _ = phaseSweepSkeletalHomotopy W 0 (p.1, (phaseSweepEdgeBasePair W 0).right p.2) := by
        apply Subtype.ext
        change constructedA2CentralCompactOrbitMap W (constructedA2CircleSweepParameter 1 p.1)
          ((phaseSweepEdgeBasePair W 0).right p.2).1 =
          constructedA2CentralCompactOrbitMap W (constructedA2CircleSweepParameter 0 p.1)
            ((phaseSweepEdgeBasePair W 0).right p.2).1
        rw [circleSweepParameter_eq_period, circleSweepParameter_eq_period,
          phaseSweepEdgeBasePair_apply]
        apply (actualLocalCuspCentralOrbitMap_isEmbedding W).injective
        rw [← cuspFillingPeriodCircle_centralOrbit, ← cuspFillingPeriodCircle_centralOrbit]
        have hb : p.2.1 = (fun _ ↦ p.2.1 0) := by ext j; fin_cases j; rfl
        rw [hb, ← phaseSweepToFilling_zero_fourth, ← phaseSweepToFilling_zero]
      _ = _ := phaseSweepForwardCylinderPair_reverse W 0 p
  rw [phaseSweepRelativePrism_edge_of_cylinder T W 0 1 (phaseSweepForwardCylinderPair W 0) hp]
  exact (phaseSweepRelativePrism_edge T W 0).symm

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
