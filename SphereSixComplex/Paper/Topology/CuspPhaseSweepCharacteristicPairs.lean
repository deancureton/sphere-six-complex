module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepParameterComparison
public import SphereSixComplex.Prerequisites.Topology.OrientedIntervalCylinderPrism

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory HomologicalComplex
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction CuspFilling CuspPeriodExpansion
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepCellIndex (i : Fin 3) : Fin 4 := i.succ

public def phaseSweepCharacteristicPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    CWTopologicalPairMap (cwCharacteristicBoundaryInclusion 2)
      (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let P := integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 2
    (phaseSweepCellIndex i)
  exact ⟨P.boundaryMap, P.diskMap, P.comm⟩

public theorem phaseSweepCharacteristicPair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3)
    (b : CWCharacteristicClosedBall 2) :
    ((phaseSweepCharacteristicPair W i).right b).1 = phaseSweepOrbit W i b.1 := by
  fin_cases i <;> rfl

public def phaseSweepCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet 1))
      (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact
    { left := (cwCharacteristicCylinderPair 1).left ≫ (phaseSweepCharacteristicPair W i).left
      right := (cwCharacteristicCylinderPair 1).right ≫ (phaseSweepCharacteristicPair W i).right
      comm := rfl }

public theorem phaseSweepCylinderPair_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3)
    (p : unitInterval × CWCharacteristicClosedBall 1) :
    ((phaseSweepCylinderPair W i).right p).1 =
      phaseSweepOrbit W i ![p.2.1 0, 2 * (p.1 : ℝ) - 1] := by
  change ((phaseSweepCharacteristicPair W i).right
    (cwCharacteristicCylinderHomeomorph 1 p)).1 = _
  rw [phaseSweepCharacteristicPair_apply, cwCharacteristicCylinderHomeomorph_apply]
  congr 1
  ext j
  fin_cases j <;> rfl




public theorem phaseSweepCylinderPair_relativeChainMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    cwRelativeIntegralSingularChainMapOfPair (phaseSweepCylinderPair W i) =
      (cwCharacteristicCylinderRelativeIso 1).hom ≫
        cwRelativeIntegralSingularChainMapOfPair (phaseSweepCharacteristicPair W i) :=
  cwRelativeIntegralSingularChainMapOfPair_comp (cwCharacteristicCylinderPair 1)
    (phaseSweepCharacteristicPair W i)

public def phaseSweepCylinderGenerator (T : CellularHomology.IntegralComparison) :
    (cwRelativeIntegralSingularChainComplex
      (cylinderBoundaryInclusion (cwBallBoundarySet 1))).homology 2 :=
  homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2 ((T.diskOrientation 2).symm 1)

public theorem phaseSweepCylinderGenerator_image
    (T : CellularHomology.IntegralComparison)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepCylinderPair W i)) 2
      (phaseSweepCylinderGenerator T) =
        T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2
          (Finsupp.single (phaseSweepCellIndex i) 1) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  rw [phaseSweepCylinderPair_relativeChainMap, homologyMap_comp]
  change homologyMap (cwRelativeIntegralSingularChainMapOfPair
    (phaseSweepCharacteristicPair W i)) 2
      (homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2
        (homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2
          ((T.diskOrientation 2).symm 1))) = _
  have he : homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2
      (homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2
        ((T.diskOrientation 2).symm 1)) = (T.diskOrientation 2).symm 1 := by
    change (homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2 ≫
      homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2) _ = _
    rw [← homologyMap_comp, Iso.inv_hom_id, homologyMap_id]
    rfl
  rw [he]
  exact (T.cellBasis_single (ActualLocalCuspCentralOrbitQuotient W) 2
    (phaseSweepCellIndex i)).symm


public theorem phaseSweepOrientedPrism_images
    (T : CellularHomology.IntegralComparison) :
    ∃ u : ℤ, (u = 1 ∨ u = -1) ∧
      ∀ (W : ActualPuncturedCuspCollarWitness N constructedModel)
        [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3),
        let _ := (phaseSweepCellAtlas W).cwComplex
        homologyMap (cwRelativeIntegralSingularChainMapOfPair (phaseSweepCylinderPair W i)) 2
          orientedIntervalCylinderPrism =
            u • T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2
              (Finsupp.single (phaseSweepCellIndex i) 1) := by
  rcases orientedIntervalCylinderPrism_eq_orientation_or_neg_orientation T with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro W _ i
    let _ := (phaseSweepCellAtlas W).cwComplex
    dsimp only
    change orientedIntervalCylinderPrism = phaseSweepCylinderGenerator T at h
    rw [h, phaseSweepCylinderGenerator_image]
    exact (one_zsmul _).symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro W _ i
    let _ := (phaseSweepCellAtlas W).cwComplex
    dsimp only
    change orientedIntervalCylinderPrism = -phaseSweepCylinderGenerator T at h
    rw [h, map_neg, phaseSweepCylinderGenerator_image]
    exact (neg_one_zsmul _).symm

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
