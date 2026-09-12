module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.BoundaryDeckAttachment

@[expose] public section

noncomputable section
open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

namespace Construction

public def correctedPositiveTwoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  effectivePhaseCentralOrbit W
    (actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 x))
    (correctedPositiveHexagonMap W.localWitness.radius_pos 0 x)

public theorem correctedPositiveTwoOrbit_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) :
    correctedPositiveTwoOrbit W x.1 = boundaryCorrectedBallOrbit W x := by
  unfold correctedPositiveTwoOrbit boundaryCorrectedBallOrbit
  rw [correctedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 x.1 x.property]
  rfl

public theorem continuousOn_correctedPositiveTwoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (correctedPositiveTwoOrbit W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
      (correctedPositiveTwoOrbit W) = boundaryCorrectedBallOrbit W := by
    funext x
    exact correctedPositiveTwoOrbit_closedBall W x
  rw [heq]
  exact continuous_boundaryCorrectedBallOrbit W

public theorem correctedPositiveTwoOrbit_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (correctedPositiveTwoOrbit W) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) := by
  intro x hx
  rw [correctedPositiveTwoOrbit_closedBall W
    ⟨x, Metric.sphere_subset_closedBall hx⟩]
  exact boundaryCorrectedBallOrbit_boundary_mem_oneSkeleton W _ hx

public theorem correctedPositiveTwoOrbit_ball_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1) :
    correctedPositiveTwoOrbit W x.1 =
      (actualSingletonBallPhaseHomeomorph W
        (x, actualBoundaryGauge (N := N)
          (correctedHexagonHomeomorph 0 x.1))).1 := by
  rw [correctedPositiveTwoOrbit_closedBall W
    ⟨x.1, Metric.ball_subset_closedBall x.property⟩]
  rfl

public theorem isEmbedding_correctedPositiveTwoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (correctedPositiveTwoOrbit W)) := by
  let g : Metric.ball (0 : Fin 2 → ℝ) 1 → Fin 2 → Circle := fun x ↦
    actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 x.1)
  have hg : Continuous g := (continuous_boundaryCompactGauge _ _).comp
    ((correctedHexagonHomeomorph 0).continuous.comp continuous_subtype_val)
  have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (correctedPositiveTwoOrbit W) =
      Subtype.val ∘ (actualSingletonBallPhaseHomeomorph W) ∘ (fun x ↦ (x, g x)) := by
    funext x
    exact correctedPositiveTwoOrbit_ball_formula W x
  rw [heq]
  exact IsEmbedding.subtypeVal.comp
    ((actualSingletonBallPhaseHomeomorph W).isEmbedding.comp (isEmbedding_graph hg))

public theorem correctedPositiveTwoOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (correctedPositiveTwoOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy h
  have heq : (⟨x, hx⟩ : Metric.ball (0 : Fin 2 → ℝ) 1) = ⟨y, hy⟩ :=
    (isEmbedding_correctedPositiveTwoOrbit W).injective h
  exact congrArg Subtype.val heq

public def correctedPositiveTwoCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (correctedPositiveTwoOrbit W) (Metric.ball 0 1)
    (correctedPositiveTwoOrbit_injOn W)

public theorem correctedPositiveTwoCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (correctedPositiveTwoCell W).source = Metric.ball 0 1 := rfl

public theorem continuousOn_correctedPositiveTwoCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (correctedPositiveTwoCell W) (Metric.closedBall 0 1) :=
  continuousOn_correctedPositiveTwoOrbit W

public theorem continuousOn_correctedPositiveTwoCell_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (correctedPositiveTwoCell W).symm
      (correctedPositiveTwoCell W).target := by
  let e := correctedPositiveTwoCell W
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (isEmbedding_correctedPositiveTwoOrbit W).continuous_iff.mpr
    have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (correctedPositiveTwoOrbit W) ∘ lift =
          (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 2 → ℝ))
  exact continuous_subtype_val.comp hlift

public theorem correctedPositiveTwoCell_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (correctedPositiveTwoCell W) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) :=
  correctedPositiveTwoOrbit_mapsTo_oneSkeleton W

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
