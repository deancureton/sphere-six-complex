module

public import SphereSixComplex.Prerequisites.Topology.CircleCellProduct
public import SphereSixComplex.Prerequisites.Topology.SupNormBallBoundary
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CorrectedPositiveTwoCell
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PhaseBallBoundary

@[expose] public section

noncomputable section
open Function Set Topology Matrix Real

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

namespace Construction

public def gaugeProductHomeomorph :
    (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) where
  toFun p := (p.1, actualBoundaryGauge (N := N)
    (correctedHexagonHomeomorph 0 p.1.1) * p.2)
  invFun p := (p.1, (actualBoundaryGauge (N := N)
    (correctedHexagonHomeomorph 0 p.1.1))⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    apply continuous_fst.prodMk
    apply Continuous.mul _ continuous_snd
    exact (continuous_boundaryCompactGauge _ _).comp
      ((correctedHexagonHomeomorph 0).continuous.comp
        (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    apply continuous_fst.prodMk
    apply Continuous.mul _ continuous_snd
    apply Continuous.inv
    exact (continuous_boundaryCompactGauge _ _).comp
      ((correctedHexagonHomeomorph 0).continuous.comp
        (continuous_subtype_val.comp continuous_fst))

public def correctedSingletonProductHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) ≃ₜ
      actualSingletonStratum W :=
  (gaugeProductHomeomorph (N := N)).trans (actualSingletonBallPhaseHomeomorph W)

public def correctedPhaseOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle) (x : Fin (2 + n) → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  let p := (Fin.appendHomeomorph (X := ℝ) 2 n).symm x
  effectivePhaseCentralOrbit W
    (actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 p.1) *
      phase p.2)
    (correctedPositiveHexagonMap W.localWitness.radius_pos 0 p.1)

public theorem correctedPhaseOrbit_ball_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin (2 + n) → ℝ) 1) :
    correctedPhaseOrbit W n phase x.1 =
      (correctedSingletonProductHomeomorph W
        ((SupNormBall.prodHomeomorph 2 n x).1,
          phase (SupNormBall.prodHomeomorph 2 n x).2.1)).1 := by
  change effectivePhaseCentralOrbit W
    (actualBoundaryGauge (N := N)
      (correctedHexagonHomeomorph 0 (SupNormBall.prodHomeomorph 2 n x).1.1) *
        phase (SupNormBall.prodHomeomorph 2 n x).2.1)
    (correctedPositiveHexagonMap W.localWitness.radius_pos 0
      (SupNormBall.prodHomeomorph 2 n x).1.1) = _
  rw [correctedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 _
      (Metric.ball_subset_closedBall (SupNormBall.prodHomeomorph 2 n x).1.property)]
  rfl

public theorem isEmbedding_correctedPhaseOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    IsEmbedding ((Metric.ball (0 : Fin (2 + n) → ℝ) 1).domRestrict
      (correctedPhaseOrbit W n phase)) := by
  let f : (Metric.ball (0 : Fin 2 → ℝ) 1) × (Metric.ball (0 : Fin n → ℝ) 1) →
      (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) := fun p ↦ (p.1, phase p.2.1)
  have hf : IsEmbedding f := IsEmbedding.id.prodMap hphase
  have heq : (Metric.ball (0 : Fin (2 + n) → ℝ) 1).domRestrict
      (correctedPhaseOrbit W n phase) =
      Subtype.val ∘ (correctedSingletonProductHomeomorph W) ∘
        f ∘ (SupNormBall.prodHomeomorph 2 n) := by
    funext x
    exact correctedPhaseOrbit_ball_formula W n phase x
  rw [heq]
  exact IsEmbedding.subtypeVal.comp
    ((correctedSingletonProductHomeomorph W).isEmbedding.comp
      (hf.comp (SupNormBall.prodHomeomorph 2 n).isEmbedding))

public def correctedThreeOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    (Fin 3 → ℝ) → ActualLocalCuspCentralOrbitQuotient W :=
  correctedPhaseOrbit W 1 (CircleCell.onePhase i)

public def correctedFourOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Fin 4 → ℝ) → ActualLocalCuspCentralOrbitQuotient W :=
  correctedPhaseOrbit W 2 CircleCell.twoPhase



public theorem continuousOn_correctedPhaseOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle) (hphase : Continuous phase) :
    ContinuousOn (correctedPhaseOrbit W n phase) (Metric.closedBall 0 1) := by
  let base : Metric.closedBall (0 : Fin (2 + n) → ℝ) 1 →
      Metric.closedBall (0 : Fin 2 → ℝ) 1 := fun x ↦
    ⟨((Fin.appendHomeomorph (X := ℝ) 2 n).symm x.1).1,
      ((SupNormBall.split_mem_closedBall_iff 2 n x.1).mp x.property).1⟩
  have hbase : Continuous base :=
    (((Fin.appendHomeomorph (X := ℝ) 2 n).symm.continuous.comp continuous_subtype_val).fst).subtype_mk _
  let k : Metric.closedBall (0 : Fin (2 + n) → ℝ) 1 → Fin 2 → Circle := fun x ↦
    actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 (base x).1) *
      phase (((Fin.appendHomeomorph (X := ℝ) 2 n).symm x.1).2)
  have hk : Continuous k :=
    ((continuous_boundaryCompactGauge _ _).comp
      ((correctedHexagonHomeomorph 0).continuous.comp hbase.subtype_val)).mul
      (hphase.comp ((Fin.appendHomeomorph (X := ℝ) 2 n).symm.continuous.comp
        continuous_subtype_val).snd)
  let f : Metric.closedBall (0 : Fin (2 + n) → ℝ) 1 →
      ClosedPhaseCell W.localWitness.radius := fun x ↦
    (closedBallPositiveCellHomeomorph W (base x), k x)
  have hf : Continuous f :=
    ((closedBallPositiveCellHomeomorph W).continuous.comp hbase).prodMk hk
  have heq : (Metric.closedBall (0 : Fin (2 + n) → ℝ) 1).domRestrict
      (correctedPhaseOrbit W n phase) = closedPhaseCellMap W ∘ f := by
    funext x
    change effectivePhaseCentralOrbit W (k x)
      (correctedPositiveHexagonMap W.localWitness.radius_pos 0 (base x).1) =
      effectivePhaseCentralOrbit W (k x)
        (closedBallPositiveCellHomeomorph W (base x)).1
    rw [correctedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos 0 (base x).1 (base x).property]
    rfl
  rw [continuousOn_iff_continuous_domRestrict, heq]
  exact (continuous_closedPhaseCellMap W).comp hf

public theorem continuousOn_correctedThreeOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (correctedThreeOrbit W i) (Metric.closedBall 0 1) :=
  continuousOn_correctedPhaseOrbit W 1 _ (CircleCell.continuous_onePhase i)

public theorem continuousOn_correctedFourOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (correctedFourOrbit W) (Metric.closedBall 0 1) :=
  continuousOn_correctedPhaseOrbit W 2 _ CircleCell.continuous_twoPhase

public theorem correctedPhaseOrbit_base_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle) (x : Fin (2 + n) → ℝ)
    (hx : ((Fin.appendHomeomorph (X := ℝ) 2 n).symm x).1 ∈ Metric.sphere 0 1) :
    correctedPhaseOrbit W n phase x ∈ constructedCentralBoundaryTwoSkeleton W := by
  let b : Metric.closedBall (0 : Fin 2 → ℝ) 1 :=
    ⟨((Fin.appendHomeomorph (X := ℝ) 2 n).symm x).1, Metric.sphere_subset_closedBall hx⟩
  change effectivePhaseCentralOrbit W _
    (correctedPositiveHexagonMap W.localWitness.radius_pos 0 b.1) ∈ _
  rw [correctedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 b.1 b.property]
  exact effectivePhaseBall_boundary_mem_boundaryTwoSkeleton W b hx _

public def correctedTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedCentralBoundaryTwoSkeleton W ∪
    correctedPositiveTwoOrbit W '' Metric.closedBall 0 1

public theorem correctedThreeOrbit_mapsTo_twoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    MapsTo (correctedThreeOrbit W i) (Metric.sphere 0 1)
      (correctedTwoSkeleton W) := by
  intro x hx
  rcases SupNormBall.split_mem_sphere 2 1 x hx with hbase | hphase
  · exact Or.inl (correctedPhaseOrbit_base_boundary W 1 _ x hbase)
  · apply Or.inr
    refine ⟨((Fin.appendHomeomorph (X := ℝ) 2 1).symm x).1,
      ((SupNormBall.split_mem_closedBall_iff 2 1 x).mp (Metric.sphere_subset_closedBall hx)).1, ?_⟩
    change correctedPositiveTwoOrbit W _ =
      effectivePhaseCentralOrbit W _ _
    rw [CircleCell.onePhase_eq_one_of_mem_sphere i _ hphase, mul_one]
    rfl

public def correctedThreeSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  correctedTwoSkeleton W ∪
    ⋃ i : Fin 2, correctedThreeOrbit W i '' Metric.closedBall 0 1

public theorem correctedFourOrbit_mapsTo_threeSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (correctedFourOrbit W) (Metric.sphere 0 1)
      (correctedThreeSkeleton W) := by
  intro x hx
  let p := (Fin.appendHomeomorph (X := ℝ) 2 2).symm x
  have hc := (SupNormBall.split_mem_closedBall_iff 2 2 x).mp (Metric.sphere_subset_closedBall hx)
  rcases SupNormBall.split_mem_sphere 2 2 x hx with hbase | hphase
  · exact Or.inl (Or.inl (correctedPhaseOrbit_base_boundary W 2 _ x hbase))
  · obtain ⟨i, t, ht, heq⟩ := CircleCell.exists_twoPhase_eq_onePhase p.2 hphase
    apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨i, (Fin.appendHomeomorph (X := ℝ) 2 1) (p.1, t), ?_, ?_⟩
    · exact (SupNormBall.append_mem_closedBall_iff 2 1 (p.1, t)).mpr ⟨hc.1, ht⟩
    · unfold correctedThreeOrbit correctedFourOrbit
        correctedPhaseOrbit
      rw [(Fin.appendHomeomorph (X := ℝ) 2 1).symm_apply_apply]
      change effectivePhaseCentralOrbit W
        (actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 p.1) *
          CircleCell.onePhase i t) _ =
        effectivePhaseCentralOrbit W
        (actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 p.1) *
          CircleCell.twoPhase p.2) _
      rw [heq]

public theorem correctedPhaseOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    Set.InjOn (correctedPhaseOrbit W n phase) (Metric.ball 0 1) := by
  intro x hx y hy h
  have heq : (⟨x, hx⟩ : Metric.ball (0 : Fin (2 + n) → ℝ) 1) = ⟨y, hy⟩ :=
    (isEmbedding_correctedPhaseOrbit W n phase hphase).injective h
  exact congrArg Subtype.val heq

public def correctedPhaseCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    PartialEquiv (Fin (2 + n) → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (correctedPhaseOrbit W n phase) (Metric.ball 0 1)
    (correctedPhaseOrbit_injOn W n phase hphase)

public theorem continuousOn_correctedPhaseCell_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    ContinuousOn (correctedPhaseCell W n phase hphase).symm
      (correctedPhaseCell W n phase hphase).target := by
  let e := correctedPhaseCell W n phase hphase
  let lift : e.target → Metric.ball (0 : Fin (2 + n) → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (isEmbedding_correctedPhaseOrbit W n phase hphase).continuous_iff.mpr
    have heq : (Metric.ball (0 : Fin (2 + n) → ℝ) 1).domRestrict
        (correctedPhaseOrbit W n phase) ∘ lift =
          (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin (2 + n) → ℝ))
  exact continuous_subtype_val.comp hlift

public def correctedThreeCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    PartialEquiv (Fin 3 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  correctedPhaseCell W 1 (CircleCell.onePhase i)
    (CircleCell.isEmbedding_onePhase i)

public def correctedFourCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 4 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  correctedPhaseCell W 2 CircleCell.twoPhase CircleCell.isEmbedding_twoPhase

public theorem correctedThreeCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    (correctedThreeCell W i).source = Metric.ball 0 1 := rfl

public theorem correctedFourCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (correctedFourCell W).source = Metric.ball 0 1 := rfl

public theorem continuousOn_correctedThreeCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (correctedThreeCell W i) (Metric.closedBall 0 1) :=
  continuousOn_correctedThreeOrbit W i

public theorem continuousOn_correctedFourCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (correctedFourCell W) (Metric.closedBall 0 1) :=
  continuousOn_correctedFourOrbit W

public theorem continuousOn_correctedThreeCell_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (correctedThreeCell W i).symm
      (correctedThreeCell W i).target :=
  continuousOn_correctedPhaseCell_symm W 1 _ (CircleCell.isEmbedding_onePhase i)

public theorem continuousOn_correctedFourCell_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (correctedFourCell W).symm (correctedFourCell W).target :=
  continuousOn_correctedPhaseCell_symm W 2 _ CircleCell.isEmbedding_twoPhase

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
