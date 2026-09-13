module

public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryAction
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberCoverMaps
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryAttachingLoop
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods SphereSixComplex.StandardTorusHomology
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def centralBoundaryPole (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    centralBoundary W :=
  ⟨CentralBoundary.axisOrbit W false 0 0,
    CentralBoundary.axisOrbit_not_mem_singletonPhaseImage W false 0 0⟩

@[simp] public theorem centralBoundaryPhaseMap_pole
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : Fin 2 → Circle) :
    centralBoundaryPhaseMap W (k, centralBoundaryPole W) = centralBoundaryPole W := by
  apply Subtype.ext
  change centralCompactOrbitMap W k (CentralBoundary.axisOrbit W false 0 0) = _
  rw [CentralBoundary.axisOrbit_zero, centralCompactOrbitMap_origin]
  exact (CentralBoundary.axisOrbit_zero W false 0).symm

public def centralBoundaryOrbitMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    {X : Type} [TopologicalSpace X] (k : C(X, Fin 2 → Circle)) (b : centralBoundary W) :
    C(X, centralBoundary W) :=
  (centralBoundaryPhaseMap W).comp ⟨fun x ↦ (k x, b), k.continuous.prodMk continuous_const⟩

public def centralBoundaryOrbitHomotopy
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    {X : Type} [TopologicalSpace X] (k : C(X, Fin 2 → Circle)) (b : centralBoundary W) :
    ContinuousMap.Homotopy (centralBoundaryOrbitMap W k b)
      (ContinuousMap.const X (centralBoundaryPole W)) where
  toFun p := centralBoundaryPhaseMap W (k p.2, (PathConnectedSpace.somePath b (centralBoundaryPole W)) p.1)
  continuous_toFun := (centralBoundaryPhaseMap W).continuous.comp
    ((k.continuous.comp continuous_snd).prodMk
      ((PathConnectedSpace.somePath b (centralBoundaryPole W)).continuous.comp continuous_fst))
  map_zero_left x := by simp [centralBoundaryOrbitMap]
  map_one_left x := by simp

public theorem centralBoundaryOrbitMap_homology_eq_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    {X : Type} [TopologicalSpace X] (k : C(X, Fin 2 → Circle)) (b : centralBoundary W)
    (n : ℕ) (hn : n ≠ 0) : integralSingularHomologyMap n (centralBoundaryOrbitMap W k b) = 0 := by
  rw [integralSingularHomologyMap_eq_of_homotopy n (centralBoundaryOrbitHomotopy W k b)]
  let _ := subsingleton_integralSingularHomology_of_contractible (X := Unit) n hn
  have h : ContinuousMap.const X (centralBoundaryPole W) =
      (ContinuousMap.const Unit (centralBoundaryPole W)).comp (ContinuousMap.const X ()) := rfl
  rw [h]
  ext x
  rw [← integralSingularHomologyMap_comp_wang]
  rw [Subsingleton.elim (integralSingularHomologyMap n (ContinuousMap.const X ()) x) 0, map_zero]
  rfl

public theorem centralSphereAttachingMap_unphased
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.sphere (0 : Fin 2 → ℝ) 1) :
    centralSphereAttachingMap W (x, 1) = correctedBallBoundaryMap W x := by
  apply Subtype.ext
  exact centralDiskMap_one W _

public def centralUnphasedAttachingCircle
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(StdTorus 1, centralBoundary W) :=
  (correctedBallBoundaryMap W).comp
    ⟨fun z ↦ supNormUnitSphereCircleHomeomorph.symm
      (AddCircle.homeomorphCircle one_ne_zero (z 0)), by fun_prop⟩

public theorem centralUnphasedAttachingCircle_homologyOne_eq_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    integralSingularHomologyMap 1 (centralUnphasedAttachingCircle W) = 0 := by
  unfold centralUnphasedAttachingCircle
  ext x
  rw [← integralSingularHomologyMap_comp_wang,
    correctedBallBoundaryMap_homologyOne_eq_zero]
  rfl

public theorem centralTorusAttachingMap_eq_phase
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (z : StdTorus 3) :
    centralTorusAttachingMap W z = centralBoundaryPhaseMap W
      ((fun i ↦ AddCircle.homeomorphCircle one_ne_zero (z i.succ)),
        centralUnphasedAttachingCircle W (fun _ ↦ z 0)) := by
  rw [centralTorusAttachingMap_apply]
  change centralAttachingMap W _ = _
  rw [centralAttachingMap_eq_phase]
  apply congrArg (centralBoundaryPhaseMap W)
  apply Prod.ext
  · rfl
  · exact centralSphereAttachingMap_unphased W _

public theorem centralTorusAttachingMap_homologyOne_coordinate_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    integralSingularHomologyMap 1 (centralTorusAttachingMap W)
      (standardThreeTorusCoordinateHomologyClass i) = 0 := by
  change integralSingularHomologyMap 1 (centralTorusAttachingMap W)
    (integralSingularHomologyMap 1 (standardThreeTorusCoordinateCircle i)
      standardCircleHomologyGenerator) = 0
  rw [integralSingularHomologyMap_comp_wang]
  fin_cases i
  · have he : (centralTorusAttachingMap W).comp (standardThreeTorusCoordinateCircle 0) =
        centralUnphasedAttachingCircle W := by
      apply ContinuousMap.ext
      intro z
      rw [ContinuousMap.comp_apply, centralTorusAttachingMap_apply]
      have hk : (fun i : Fin 2 ↦ AddCircle.homeomorphCircle one_ne_zero
          (standardThreeTorusCoordinateCircle 0 z i.succ)) = 1 := by
        funext j
        fin_cases j <;>
          change AddCircle.homeomorphCircle one_ne_zero (0 : UnitAddCircle) = 1 <;>
          simp [AddCircle.homeomorphCircle_apply]
      rw [hk]
      exact centralSphereAttachingMap_unphased W _
    change integralSingularHomologyMap 1
      ((centralTorusAttachingMap W).comp (standardThreeTorusCoordinateCircle 0))
      standardCircleHomologyGenerator = 0
    rw [he, centralUnphasedAttachingCircle_homologyOne_eq_zero]
    rfl
  · let k : C(StdTorus 1, Fin 2 → Circle) :=
      ⟨fun z i ↦ AddCircle.homeomorphCircle one_ne_zero
        (standardThreeTorusCoordinateCircle 1 z i.succ), by fun_prop⟩
    have he : (centralTorusAttachingMap W).comp (standardThreeTorusCoordinateCircle 1) =
        centralBoundaryOrbitMap W k (centralUnphasedAttachingCircle W 0) := by
      apply ContinuousMap.ext
      intro z
      rw [ContinuousMap.comp_apply, centralTorusAttachingMap_eq_phase]
      rfl
    change integralSingularHomologyMap 1
      ((centralTorusAttachingMap W).comp (standardThreeTorusCoordinateCircle 1))
      standardCircleHomologyGenerator = 0
    rw [he, centralBoundaryOrbitMap_homology_eq_zero W k _ 1 one_ne_zero]
    rfl
  · let k : C(StdTorus 1, Fin 2 → Circle) :=
      ⟨fun z i ↦ AddCircle.homeomorphCircle one_ne_zero
        (standardThreeTorusCoordinateCircle 2 z i.succ), by fun_prop⟩
    have he : (centralTorusAttachingMap W).comp (standardThreeTorusCoordinateCircle 2) =
        centralBoundaryOrbitMap W k (centralUnphasedAttachingCircle W 0) := by
      apply ContinuousMap.ext
      intro z
      rw [ContinuousMap.comp_apply, centralTorusAttachingMap_eq_phase]
      rfl
    change integralSingularHomologyMap 1
      ((centralTorusAttachingMap W).comp (standardThreeTorusCoordinateCircle 2))
      standardCircleHomologyGenerator = 0
    rw [he, centralBoundaryOrbitMap_homology_eq_zero W k _ 1 one_ne_zero]
    rfl

public theorem centralTorusAttachingMap_homologyOne_eq_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    integralSingularHomologyMap 1 (centralTorusAttachingMap W) = 0 := by
  let _ := AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  ext x
  rw [homologyOne_eq_sum_coordinateClasses x, map_sum]
  simp only [map_zsmul, centralTorusAttachingMap_homologyOne_coordinate_zero,
    smul_zero, Finset.sum_const_zero, AddMonoidHom.zero_apply]

open SphereSixComplex.Topology.PositiveCircleCross
open SphereSixComplex.Topology.CircleProductIdentityMappingTorus

private theorem circleSweepMap_homology_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (c : C(StdTorus 1, X)) (hc : integralSingularHomologyMap 1 c = 0)
    (sweep : C(UnitAddCircle × X, Y)) :
    integralSingularHomologyMap 2
      ((sweep.comp (circleProductMap c)).comp
        ⟨circleProdStandardCircleHomeomorph.symm,
          circleProdStandardCircleHomeomorph.symm.continuous⟩)
      standardTwoTorusHomologyGenerator = 0 := by
  rw [← integralSingularHomologyMap_comp_wang,
    ← integralSingularHomologyMap_comp_wang]
  change integralSingularHomologyMap 2 sweep (positiveCircleCross c) = 0
  rw [positiveCircleCross_eq_normalized, hc, AddMonoidHom.zero_apply, map_zero, map_zero]

private def swapCircleCoordinates : C(StdTorus 2, StdTorus 2) :=
  ⟨fun z ↦ ![z 1, z 0], by fun_prop⟩

private theorem swapCircleCoordinates_homology :
    integralSingularHomologyMap 2 swapCircleCoordinates standardTwoTorusHomologyGenerator =
      -standardTwoTorusHomologyGenerator := by
  have he : swapCircleCoordinates = standardTwoTorusMatrixMap !![0, 1; 1, 0] := by
    ext z i
    fin_cases i
    · change z 1 = ∑ b : Fin 2, (![0, 1] : Fin 2 → ℤ) b • z b
      simp [Fin.sum_univ_two]
    · change z 0 = ∑ b : Fin 2, (![1, 0] : Fin 2 → ℤ) b • z b
      simp [Fin.sum_univ_two]
  rw [he, standardTwoTorusMatrixDeterminantDegree]
  simp [Matrix.det_fin_two]

public theorem centralTorusAttachingMap_homologyTwo_coordinate_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3) :
    integralSingularHomologyMap 2 (centralTorusAttachingMap W)
      (standardThreeTorusCoordinateTwoTorusHomologyClass i) = 0 := by
  change integralSingularHomologyMap 2 (centralTorusAttachingMap W)
    (integralSingularHomologyMap 2 (standardThreeTorusCoordinateTwoTorus i)
      standardTwoTorusHomologyGenerator) = 0
  rw [integralSingularHomologyMap_comp_wang]
  fin_cases i
  · let phase : C(UnitAddCircle, Fin 2 → Circle) :=
      ⟨fun z ↦ ![AddCircle.homeomorphCircle one_ne_zero z, 1], by fun_prop⟩
    have he : ((centralTorusAttachingMap W).comp
        (standardThreeTorusCoordinateTwoTorus 0)).comp swapCircleCoordinates =
        ((centralBoundaryCircleSweep W phase).comp
          (circleProductMap (centralUnphasedAttachingCircle W))).comp
          ⟨circleProdStandardCircleHomeomorph.symm,
            circleProdStandardCircleHomeomorph.symm.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, centralTorusAttachingMap_eq_phase]
      apply congrArg (centralBoundaryPhaseMap W)
      apply Prod.ext
      · funext j
        fin_cases j
        · rfl
        · change AddCircle.homeomorphCircle one_ne_zero (0 : UnitAddCircle) = 1
          simp [AddCircle.homeomorphCircle_apply]
      · rfl
    have hz := circleSweepMap_homology_zero (centralUnphasedAttachingCircle W)
      (centralUnphasedAttachingCircle_homologyOne_eq_zero W) (centralBoundaryCircleSweep W phase)
    rw [← he, ← integralSingularHomologyMap_comp_wang,
      swapCircleCoordinates_homology, map_neg, neg_eq_zero] at hz
    exact hz
  · let phase : C(UnitAddCircle, Fin 2 → Circle) :=
      ⟨fun z ↦ ![1, AddCircle.homeomorphCircle one_ne_zero z], by fun_prop⟩
    have he : ((centralTorusAttachingMap W).comp
        (standardThreeTorusCoordinateTwoTorus 1)).comp swapCircleCoordinates =
        ((centralBoundaryCircleSweep W phase).comp
          (circleProductMap (centralUnphasedAttachingCircle W))).comp
          ⟨circleProdStandardCircleHomeomorph.symm,
            circleProdStandardCircleHomeomorph.symm.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, centralTorusAttachingMap_eq_phase]
      apply congrArg (centralBoundaryPhaseMap W)
      apply Prod.ext
      · funext j
        fin_cases j
        · change AddCircle.homeomorphCircle one_ne_zero (0 : UnitAddCircle) = 1
          simp [AddCircle.homeomorphCircle_apply]
        · rfl
      · rfl
    have hz := circleSweepMap_homology_zero (centralUnphasedAttachingCircle W)
      (centralUnphasedAttachingCircle_homologyOne_eq_zero W) (centralBoundaryCircleSweep W phase)
    rw [← he, ← integralSingularHomologyMap_comp_wang,
      swapCircleCoordinates_homology, map_neg, neg_eq_zero] at hz
    exact hz
  · let k : C(StdTorus 2, Fin 2 → Circle) :=
      ⟨fun z i ↦ AddCircle.homeomorphCircle one_ne_zero (z i), by fun_prop⟩
    have he : (centralTorusAttachingMap W).comp (standardThreeTorusCoordinateTwoTorus 2) =
        centralBoundaryOrbitMap W k (centralUnphasedAttachingCircle W 0) := by
      apply ContinuousMap.ext
      intro z
      rw [ContinuousMap.comp_apply, centralTorusAttachingMap_eq_phase]
      rfl
    change integralSingularHomologyMap 2
      ((centralTorusAttachingMap W).comp (standardThreeTorusCoordinateTwoTorus 2))
      standardTwoTorusHomologyGenerator = 0
    rw [he, centralBoundaryOrbitMap_homology_eq_zero W k _ 2 (by omega)]
    rfl

public theorem centralTorusAttachingMap_homologyTwo_eq_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    integralSingularHomologyMap 2 (centralTorusAttachingMap W) = 0 := by
  let _ := AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  ext x
  rw [homologyTwo_eq_sum_coordinateClasses x, map_sum]
  simp only [map_zsmul, centralTorusAttachingMap_homologyTwo_coordinate_zero,
    smul_zero, Finset.sum_const_zero, AddMonoidHom.zero_apply]

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
