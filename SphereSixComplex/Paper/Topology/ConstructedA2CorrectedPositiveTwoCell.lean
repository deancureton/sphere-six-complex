module

public import SphereSixComplex.Paper.Topology.ConstructedA2BoundaryDeckAttachment

@[expose] public section

noncomputable section
open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedA2CorrectedPositiveTwoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2EffectivePhaseCentralOrbit W
    (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 x))
    (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos 0 x)

public theorem constructedA2CorrectedPositiveTwoOrbit_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) :
    constructedA2CorrectedPositiveTwoOrbit W x.1 = constructedA2BoundaryCorrectedBallOrbit W x := by
  unfold constructedA2CorrectedPositiveTwoOrbit constructedA2BoundaryCorrectedBallOrbit
  rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 x.1 x.property]
  rfl

public theorem constructedA2CorrectedPositiveTwoOrbit_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2CorrectedPositiveTwoOrbit W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
      (constructedA2CorrectedPositiveTwoOrbit W) = constructedA2BoundaryCorrectedBallOrbit W := by
    funext x
    exact constructedA2CorrectedPositiveTwoOrbit_closedBall W x
  rw [heq]
  exact constructedA2BoundaryCorrectedBallOrbit_continuous W

public theorem constructedA2CorrectedPositiveTwoOrbit_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedA2CorrectedPositiveTwoOrbit W) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) := by
  intro x hx
  rw [constructedA2CorrectedPositiveTwoOrbit_closedBall W
    ⟨x, Metric.sphere_subset_closedBall hx⟩]
  exact constructedA2BoundaryCorrectedBallOrbit_boundary_mem_oneSkeleton W _ hx

public theorem constructedA2CorrectedPositiveTwoOrbit_ball_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1) :
    constructedA2CorrectedPositiveTwoOrbit W x.1 =
      (constructedA2ActualSingletonBallPhaseHomeomorph W
        (x, constructedA2ActualBoundaryGauge (N := N)
          (constructedA2CorrectedHexagonHomeomorph 0 x.1))).1 := by
  rw [constructedA2CorrectedPositiveTwoOrbit_closedBall W
    ⟨x.1, Metric.ball_subset_closedBall x.property⟩]
  rfl

public theorem constructedA2CorrectedPositiveTwoOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (constructedA2CorrectedPositiveTwoOrbit W)) := by
  let g : Metric.ball (0 : Fin 2 → ℝ) 1 → Fin 2 → Circle := fun x ↦
    constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 x.1)
  have hg : Continuous g := (constructedA2BoundaryCompactGauge_continuous _ _).comp
    ((constructedA2CorrectedHexagonHomeomorph 0).continuous.comp continuous_subtype_val)
  have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (constructedA2CorrectedPositiveTwoOrbit W) =
      Subtype.val ∘ (constructedA2ActualSingletonBallPhaseHomeomorph W) ∘ (fun x ↦ (x, g x)) := by
    funext x
    exact constructedA2CorrectedPositiveTwoOrbit_ball_formula W x
  rw [heq]
  exact IsEmbedding.subtypeVal.comp
    ((constructedA2ActualSingletonBallPhaseHomeomorph W).isEmbedding.comp (isEmbedding_graph hg))

public theorem constructedA2CorrectedPositiveTwoOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedA2CorrectedPositiveTwoOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy h
  have heq : (⟨x, hx⟩ : Metric.ball (0 : Fin 2 → ℝ) 1) = ⟨y, hy⟩ :=
    (constructedA2CorrectedPositiveTwoOrbit_isEmbedding W).injective h
  exact congrArg Subtype.val heq

public def constructedA2CorrectedPositiveTwoCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedA2CorrectedPositiveTwoOrbit W) (Metric.ball 0 1)
    (constructedA2CorrectedPositiveTwoOrbit_injOn W)

public theorem constructedA2CorrectedPositiveTwoCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedA2CorrectedPositiveTwoCell W).source = Metric.ball 0 1 := rfl

public theorem constructedA2CorrectedPositiveTwoCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2CorrectedPositiveTwoCell W) (Metric.closedBall 0 1) :=
  constructedA2CorrectedPositiveTwoOrbit_continuousOn W

public theorem constructedA2CorrectedPositiveTwoCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2CorrectedPositiveTwoCell W).symm
      (constructedA2CorrectedPositiveTwoCell W).target := by
  let e := constructedA2CorrectedPositiveTwoCell W
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (constructedA2CorrectedPositiveTwoOrbit_isEmbedding W).continuous_iff.mpr
    have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (constructedA2CorrectedPositiveTwoOrbit W) ∘ lift =
          (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 2 → ℝ))
  exact continuous_subtype_val.comp hlift

public theorem constructedA2CorrectedPositiveTwoCell_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedA2CorrectedPositiveTwoCell W) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) :=
  constructedA2CorrectedPositiveTwoOrbit_mapsTo_oneSkeleton W

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
