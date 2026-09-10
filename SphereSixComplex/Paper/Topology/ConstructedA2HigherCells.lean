module

public import SphereSixComplex.Prerequisites.Topology.ConstructedCircleCell
public import SphereSixComplex.Paper.Topology.ConstructedA2CorrectedPositiveTwoCell
public import SphereSixComplex.Paper.Topology.ConstructedA2PhaseBallBoundary

@[expose] public section

noncomputable section
open Function Set Topology Matrix Real

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedA2GaugeProductHomeomorph :
    (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) ≃ₜ
      (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) where
  toFun p := (p.1, constructedA2ActualBoundaryGauge (N := N)
    (constructedA2CorrectedHexagonHomeomorph 0 p.1.1) * p.2)
  invFun p := (p.1, (constructedA2ActualBoundaryGauge (N := N)
    (constructedA2CorrectedHexagonHomeomorph 0 p.1.1))⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    apply continuous_fst.prodMk
    apply Continuous.mul _ continuous_snd
    exact (constructedA2BoundaryCompactGauge_continuous _ _).comp
      ((constructedA2CorrectedHexagonHomeomorph 0).continuous.comp
        (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    apply continuous_fst.prodMk
    apply Continuous.mul _ continuous_snd
    apply Continuous.inv
    exact (constructedA2BoundaryCompactGauge_continuous _ _).comp
      ((constructedA2CorrectedHexagonHomeomorph 0).continuous.comp
        (continuous_subtype_val.comp continuous_fst))

public def constructedA2CorrectedSingletonProductHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) ≃ₜ
      constructedA2ActualSingletonStratum W :=
  (constructedA2GaugeProductHomeomorph (N := N)).trans (constructedA2ActualSingletonBallPhaseHomeomorph W)

public def constructedA2CorrectedPhaseOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle) (x : Fin (2 + n) → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  let p := (Fin.appendHomeomorph (X := ℝ) 2 n).symm x
  constructedA2EffectivePhaseCentralOrbit W
    (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 p.1) *
      phase p.2)
    (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos 0 p.1)

public theorem constructedA2CorrectedPhaseOrbit_ball_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin (2 + n) → ℝ) 1) :
    constructedA2CorrectedPhaseOrbit W n phase x.1 =
      (constructedA2CorrectedSingletonProductHomeomorph W
        ((constructedBallSplitHomeomorph 2 n x).1,
          phase (constructedBallSplitHomeomorph 2 n x).2.1)).1 := by
  change constructedA2EffectivePhaseCentralOrbit W
    (constructedA2ActualBoundaryGauge (N := N)
      (constructedA2CorrectedHexagonHomeomorph 0 (constructedBallSplitHomeomorph 2 n x).1.1) *
        phase (constructedBallSplitHomeomorph 2 n x).2.1)
    (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos 0
      (constructedBallSplitHomeomorph 2 n x).1.1) = _
  rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 _
      (Metric.ball_subset_closedBall (constructedBallSplitHomeomorph 2 n x).1.property)]
  rfl

public theorem constructedA2CorrectedPhaseOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    IsEmbedding ((Metric.ball (0 : Fin (2 + n) → ℝ) 1).domRestrict
      (constructedA2CorrectedPhaseOrbit W n phase)) := by
  let f : (Metric.ball (0 : Fin 2 → ℝ) 1) × (Metric.ball (0 : Fin n → ℝ) 1) →
      (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) := fun p ↦ (p.1, phase p.2.1)
  have hf : IsEmbedding f := IsEmbedding.id.prodMap hphase
  have heq : (Metric.ball (0 : Fin (2 + n) → ℝ) 1).domRestrict
      (constructedA2CorrectedPhaseOrbit W n phase) =
      Subtype.val ∘ (constructedA2CorrectedSingletonProductHomeomorph W) ∘
        f ∘ (constructedBallSplitHomeomorph 2 n) := by
    funext x
    exact constructedA2CorrectedPhaseOrbit_ball_formula W n phase x
  rw [heq]
  exact IsEmbedding.subtypeVal.comp
    ((constructedA2CorrectedSingletonProductHomeomorph W).isEmbedding.comp
      (hf.comp (constructedBallSplitHomeomorph 2 n).isEmbedding))

public def constructedA2CircleOnePhase (i : Fin 2) (x : Fin 1 → ℝ) : Fin 2 → Circle :=
  if i = 0 then ![constructedCircleBallCell x, 1] else ![1, constructedCircleBallCell x]

public def constructedA2CircleTwoPhase (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  fun j ↦ constructedCircleCell (x j)

public theorem constructedA2CircleOnePhase_isEmbedding (i : Fin 2) :
    IsEmbedding ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict (constructedA2CircleOnePhase i)) := by
  fin_cases i
  · exact (Homeomorph.finTwoArrow (X := Circle)).symm.isEmbedding.comp
      ((isEmbedding_prodMkLeft (1 : Circle)).comp constructedCircleBallCell_isEmbedding)
  · exact (Homeomorph.finTwoArrow (X := Circle)).symm.isEmbedding.comp
      ((isEmbedding_prodMkRight (1 : Circle)).comp constructedCircleBallCell_isEmbedding)

public theorem constructedA2CircleTwoPhase_isEmbedding :
    IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict constructedA2CircleTwoPhase) := by
  have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict constructedA2CircleTwoPhase =
      (Homeomorph.finTwoArrow (X := Circle)).symm ∘
        Prod.map ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict constructedCircleBallCell)
          ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict constructedCircleBallCell) ∘
        (constructedBallSplitHomeomorph 1 1) := by
    funext x j
    fin_cases j <;> rfl
  rw [heq]
  exact (Homeomorph.finTwoArrow (X := Circle)).symm.isEmbedding.comp
    ((constructedCircleBallCell_isEmbedding.prodMap constructedCircleBallCell_isEmbedding).comp
      (constructedBallSplitHomeomorph 1 1).isEmbedding)

public def constructedA2CorrectedThreeOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    (Fin 3 → ℝ) → ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2CorrectedPhaseOrbit W 1 (constructedA2CircleOnePhase i)

public def constructedA2CorrectedFourOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Fin 4 → ℝ) → ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2CorrectedPhaseOrbit W 2 constructedA2CircleTwoPhase

public theorem constructedA2CorrectedThreeOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    IsEmbedding ((Metric.ball (0 : Fin 3 → ℝ) 1).domRestrict
      (constructedA2CorrectedThreeOrbit W i)) :=
  constructedA2CorrectedPhaseOrbit_isEmbedding W 1 _ (constructedA2CircleOnePhase_isEmbedding i)

public theorem constructedA2CorrectedFourOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsEmbedding ((Metric.ball (0 : Fin 4 → ℝ) 1).domRestrict
      (constructedA2CorrectedFourOrbit W)) :=
  constructedA2CorrectedPhaseOrbit_isEmbedding W 2 _ constructedA2CircleTwoPhase_isEmbedding

public theorem constructedAppend_mem_closedBall (m n : ℕ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    Fin.append x.1 x.2 ∈ Metric.closedBall 0 1 ↔
      x ∈ (Metric.closedBall (0 : Fin m → ℝ) 1) ×ˢ
        (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  simp [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Fin.forall_fin_add]

public theorem constructedSplit_mem_closedBall (m n : ℕ) (x : Fin (m + n) → ℝ) :
    x ∈ Metric.closedBall 0 1 ↔
      (Fin.appendHomeomorph (X := ℝ) m n).symm x ∈
        (Metric.closedBall (0 : Fin m → ℝ) 1) ×ˢ
          (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  have h := constructedAppend_mem_closedBall m n ((Fin.appendHomeomorph (X := ℝ) m n).symm x)
  change (Fin.appendHomeomorph (X := ℝ) m n) ((Fin.appendHomeomorph (X := ℝ) m n).symm x) ∈
    Metric.closedBall 0 1 ↔ _ at h
  rw [(Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply] at h
  exact h

public theorem constructedA2CorrectedPhaseOrbit_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle) (hphase : Continuous phase) :
    ContinuousOn (constructedA2CorrectedPhaseOrbit W n phase) (Metric.closedBall 0 1) := by
  let base : Metric.closedBall (0 : Fin (2 + n) → ℝ) 1 →
      Metric.closedBall (0 : Fin 2 → ℝ) 1 := fun x ↦
    ⟨((Fin.appendHomeomorph (X := ℝ) 2 n).symm x.1).1,
      ((constructedSplit_mem_closedBall 2 n x.1).mp x.property).1⟩
  have hbase : Continuous base :=
    (((Fin.appendHomeomorph (X := ℝ) 2 n).symm.continuous.comp continuous_subtype_val).fst).subtype_mk _
  let k : Metric.closedBall (0 : Fin (2 + n) → ℝ) 1 → Fin 2 → Circle := fun x ↦
    constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 (base x).1) *
      phase (((Fin.appendHomeomorph (X := ℝ) 2 n).symm x.1).2)
  have hk : Continuous k :=
    ((constructedA2BoundaryCompactGauge_continuous _ _).comp
      ((constructedA2CorrectedHexagonHomeomorph 0).continuous.comp hbase.subtype_val)).mul
      (hphase.comp ((Fin.appendHomeomorph (X := ℝ) 2 n).symm.continuous.comp
        continuous_subtype_val).snd)
  let f : Metric.closedBall (0 : Fin (2 + n) → ℝ) 1 →
      ConstructedA2ClosedPhaseCell W.localWitness.radius := fun x ↦
    (constructedA2ClosedBallPositiveCellHomeomorph W (base x), k x)
  have hf : Continuous f :=
    ((constructedA2ClosedBallPositiveCellHomeomorph W).continuous.comp hbase).prodMk hk
  have heq : (Metric.closedBall (0 : Fin (2 + n) → ℝ) 1).domRestrict
      (constructedA2CorrectedPhaseOrbit W n phase) = constructedA2ClosedPhaseCellMap W ∘ f := by
    funext x
    change constructedA2EffectivePhaseCentralOrbit W (k x)
      (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos 0 (base x).1) =
      constructedA2EffectivePhaseCentralOrbit W (k x)
        (constructedA2ClosedBallPositiveCellHomeomorph W (base x)).1
    rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos 0 (base x).1 (base x).property]
    rfl
  rw [continuousOn_iff_continuous_domRestrict, heq]
  exact (constructedA2ClosedPhaseCellMap_continuous W).comp hf

public theorem constructedA2CircleOnePhase_continuous (i : Fin 2) :
    Continuous (constructedA2CircleOnePhase i) := by
  have h : Continuous constructedCircleBallCell := constructedCircleCell_continuous.comp (continuous_apply 0)
  fin_cases i <;> unfold constructedA2CircleOnePhase <;> dsimp <;> fun_prop

public theorem constructedA2CircleTwoPhase_continuous : Continuous constructedA2CircleTwoPhase := by
  exact continuous_pi fun j ↦ constructedCircleCell_continuous.comp (continuous_apply j)

public theorem constructedA2CorrectedThreeOrbit_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (constructedA2CorrectedThreeOrbit W i) (Metric.closedBall 0 1) :=
  constructedA2CorrectedPhaseOrbit_continuousOn W 1 _ (constructedA2CircleOnePhase_continuous i)

public theorem constructedA2CorrectedFourOrbit_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2CorrectedFourOrbit W) (Metric.closedBall 0 1) :=
  constructedA2CorrectedPhaseOrbit_continuousOn W 2 _ constructedA2CircleTwoPhase_continuous

public theorem constructedSplit_mem_ball (m n : ℕ) (x : Fin (m + n) → ℝ) :
    x ∈ Metric.ball 0 1 ↔
      (Fin.appendHomeomorph (X := ℝ) m n).symm x ∈
        (Metric.ball (0 : Fin m → ℝ) 1) ×ˢ (Metric.ball (0 : Fin n → ℝ) 1) := by
  have h := constructedAppend_mem_ball m n ((Fin.appendHomeomorph (X := ℝ) m n).symm x)
  change (Fin.appendHomeomorph (X := ℝ) m n) ((Fin.appendHomeomorph (X := ℝ) m n).symm x) ∈
    Metric.ball 0 1 ↔ _ at h
  rw [(Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply] at h
  exact h

public theorem constructedSplit_mem_sphere (m n : ℕ) (x : Fin (m + n) → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    ((Fin.appendHomeomorph (X := ℝ) m n).symm x).1 ∈ Metric.sphere 0 1 ∨
      ((Fin.appendHomeomorph (X := ℝ) m n).symm x).2 ∈ Metric.sphere 0 1 := by
  have hc := (constructedSplit_mem_closedBall m n x).mp (Metric.sphere_subset_closedBall hx)
  have hb : x ∉ Metric.ball 0 1 := Set.disjoint_left.mp Metric.sphere_disjoint_ball hx
  by_cases hleft : ((Fin.appendHomeomorph (X := ℝ) m n).symm x).1 ∈ Metric.ball 0 1
  · apply Or.inr
    rw [← Metric.closedBall_sdiff_ball]
    refine ⟨hc.2, ?_⟩
    intro hright
    exact hb ((constructedSplit_mem_ball m n x).mpr ⟨hleft, hright⟩)
  · apply Or.inl
    rw [← Metric.closedBall_sdiff_ball]
    exact ⟨hc.1, hleft⟩

public theorem constructedA2CorrectedPhaseOrbit_base_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle) (x : Fin (2 + n) → ℝ)
    (hx : ((Fin.appendHomeomorph (X := ℝ) 2 n).symm x).1 ∈ Metric.sphere 0 1) :
    constructedA2CorrectedPhaseOrbit W n phase x ∈ constructedCentralBoundaryTwoSkeleton W := by
  let b : Metric.closedBall (0 : Fin 2 → ℝ) 1 :=
    ⟨((Fin.appendHomeomorph (X := ℝ) 2 n).symm x).1, Metric.sphere_subset_closedBall hx⟩
  change constructedA2EffectivePhaseCentralOrbit W _
    (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos 0 b.1) ∈ _
  rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 b.1 b.property]
  exact constructedA2EffectivePhaseBall_boundary_mem_boundaryTwoSkeleton W b hx _

public theorem constructedA2CircleOnePhase_boundary (i : Fin 2) (x : Fin 1 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) : constructedA2CircleOnePhase i x = 1 := by
  have hn : |x 0| = 1 := by simpa [Metric.mem_sphere, dist_zero_right, Pi.norm_def] using hx
  have hx' : x 0 = -1 ∨ x 0 = 1 := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hn with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcell : constructedCircleBallCell x = 1 := by
    rcases hx' with h | h <;> simp [constructedCircleBallCell, h]
  fin_cases i <;> ext j <;> fin_cases j <;> simp [constructedA2CircleOnePhase, hcell]

public def constructedA2CorrectedTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedCentralBoundaryTwoSkeleton W ∪
    constructedA2CorrectedPositiveTwoOrbit W '' Metric.closedBall 0 1

public theorem constructedA2CorrectedThreeOrbit_mapsTo_twoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    MapsTo (constructedA2CorrectedThreeOrbit W i) (Metric.sphere 0 1)
      (constructedA2CorrectedTwoSkeleton W) := by
  intro x hx
  rcases constructedSplit_mem_sphere 2 1 x hx with hbase | hphase
  · exact Or.inl (constructedA2CorrectedPhaseOrbit_base_boundary W 1 _ x hbase)
  · apply Or.inr
    refine ⟨((Fin.appendHomeomorph (X := ℝ) 2 1).symm x).1,
      ((constructedSplit_mem_closedBall 2 1 x).mp (Metric.sphere_subset_closedBall hx)).1, ?_⟩
    change constructedA2CorrectedPositiveTwoOrbit W _ =
      constructedA2EffectivePhaseCentralOrbit W _ _
    rw [constructedA2CircleOnePhase_boundary i _ hphase, mul_one]
    rfl

public theorem constructedCircleCell_eq_one_of_abs_eq {t : ℝ} (ht : |t| = 1) :
    constructedCircleCell t = 1 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ht with h | h <;> simp [h]

public theorem constructedA2CircleTwoPhase_boundary (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    ∃ (i : Fin 2) (y : Fin 1 → ℝ), y ∈ Metric.closedBall 0 1 ∧
      constructedA2CircleTwoPhase x = constructedA2CircleOnePhase i y := by
  have hnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hle : ∀ j, |x j| ≤ 1 := fun j ↦ by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans_eq hnorm
  have hcoord : |x 0| = 1 ∨ |x 1| = 1 := by
    by_contra h
    push Not at h
    have hlt : ‖x‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr (by
      intro j
      fin_cases j
      · exact lt_of_le_of_ne (hle 0) h.1
      · exact lt_of_le_of_ne (hle 1) h.2)
    rw [hnorm] at hlt
    exact (lt_irrefl 1) hlt
  rcases hcoord with h | h
  · refine ⟨1, fun _ ↦ x 1, ?_, ?_⟩
    · have hb : |x 1| ≤ 1 := hle 1
      simpa [Metric.mem_closedBall, dist_zero_right, Pi.norm_def] using hb
    · have hc := constructedCircleCell_eq_one_of_abs_eq h
      funext j
      fin_cases j <;> simp [constructedA2CircleTwoPhase, constructedA2CircleOnePhase,
        constructedCircleBallCell, hc]
  · refine ⟨0, fun _ ↦ x 0, ?_, ?_⟩
    · have hb : |x 0| ≤ 1 := hle 0
      simpa [Metric.mem_closedBall, dist_zero_right, Pi.norm_def] using hb
    · have hc := constructedCircleCell_eq_one_of_abs_eq h
      funext j
      fin_cases j <;> simp [constructedA2CircleTwoPhase, constructedA2CircleOnePhase,
        constructedCircleBallCell, hc]

public def constructedA2CorrectedThreeSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedA2CorrectedTwoSkeleton W ∪
    ⋃ i : Fin 2, constructedA2CorrectedThreeOrbit W i '' Metric.closedBall 0 1

public theorem constructedA2CorrectedFourOrbit_mapsTo_threeSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedA2CorrectedFourOrbit W) (Metric.sphere 0 1)
      (constructedA2CorrectedThreeSkeleton W) := by
  intro x hx
  let p := (Fin.appendHomeomorph (X := ℝ) 2 2).symm x
  have hc := (constructedSplit_mem_closedBall 2 2 x).mp (Metric.sphere_subset_closedBall hx)
  rcases constructedSplit_mem_sphere 2 2 x hx with hbase | hphase
  · exact Or.inl (Or.inl (constructedA2CorrectedPhaseOrbit_base_boundary W 2 _ x hbase))
  · obtain ⟨i, t, ht, heq⟩ := constructedA2CircleTwoPhase_boundary p.2 hphase
    apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨i, (Fin.appendHomeomorph (X := ℝ) 2 1) (p.1, t), ?_, ?_⟩
    · exact (constructedAppend_mem_closedBall 2 1 (p.1, t)).mpr ⟨hc.1, ht⟩
    · unfold constructedA2CorrectedThreeOrbit constructedA2CorrectedFourOrbit
        constructedA2CorrectedPhaseOrbit
      rw [(Fin.appendHomeomorph (X := ℝ) 2 1).symm_apply_apply]
      change constructedA2EffectivePhaseCentralOrbit W
        (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 p.1) *
          constructedA2CircleOnePhase i t) _ =
        constructedA2EffectivePhaseCentralOrbit W
        (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 p.1) *
          constructedA2CircleTwoPhase p.2) _
      rw [heq]

public theorem constructedA2CorrectedPhaseOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    Set.InjOn (constructedA2CorrectedPhaseOrbit W n phase) (Metric.ball 0 1) := by
  intro x hx y hy h
  have heq : (⟨x, hx⟩ : Metric.ball (0 : Fin (2 + n) → ℝ) 1) = ⟨y, hy⟩ :=
    (constructedA2CorrectedPhaseOrbit_isEmbedding W n phase hphase).injective h
  exact congrArg Subtype.val heq

public def constructedA2CorrectedPhaseCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    PartialEquiv (Fin (2 + n) → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedA2CorrectedPhaseOrbit W n phase) (Metric.ball 0 1)
    (constructedA2CorrectedPhaseOrbit_injOn W n phase hphase)

public theorem constructedA2CorrectedPhaseCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (hphase : IsEmbedding ((Metric.ball (0 : Fin n → ℝ) 1).domRestrict phase)) :
    ContinuousOn (constructedA2CorrectedPhaseCell W n phase hphase).symm
      (constructedA2CorrectedPhaseCell W n phase hphase).target := by
  let e := constructedA2CorrectedPhaseCell W n phase hphase
  let lift : e.target → Metric.ball (0 : Fin (2 + n) → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (constructedA2CorrectedPhaseOrbit_isEmbedding W n phase hphase).continuous_iff.mpr
    have heq : (Metric.ball (0 : Fin (2 + n) → ℝ) 1).domRestrict
        (constructedA2CorrectedPhaseOrbit W n phase) ∘ lift =
          (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin (2 + n) → ℝ))
  exact continuous_subtype_val.comp hlift

public def constructedA2CorrectedThreeCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    PartialEquiv (Fin 3 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedA2CorrectedPhaseCell W 1 (constructedA2CircleOnePhase i)
    (constructedA2CircleOnePhase_isEmbedding i)

public def constructedA2CorrectedFourCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 4 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedA2CorrectedPhaseCell W 2 constructedA2CircleTwoPhase constructedA2CircleTwoPhase_isEmbedding

public theorem constructedA2CorrectedThreeCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    (constructedA2CorrectedThreeCell W i).source = Metric.ball 0 1 := rfl

public theorem constructedA2CorrectedFourCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedA2CorrectedFourCell W).source = Metric.ball 0 1 := rfl

public theorem constructedA2CorrectedThreeCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (constructedA2CorrectedThreeCell W i) (Metric.closedBall 0 1) :=
  constructedA2CorrectedThreeOrbit_continuousOn W i

public theorem constructedA2CorrectedFourCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2CorrectedFourCell W) (Metric.closedBall 0 1) :=
  constructedA2CorrectedFourOrbit_continuousOn W

public theorem constructedA2CorrectedThreeCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    ContinuousOn (constructedA2CorrectedThreeCell W i).symm
      (constructedA2CorrectedThreeCell W i).target :=
  constructedA2CorrectedPhaseCell_continuousOn_symm W 1 _ (constructedA2CircleOnePhase_isEmbedding i)

public theorem constructedA2CorrectedFourCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedA2CorrectedFourCell W).symm (constructedA2CorrectedFourCell W).target :=
  constructedA2CorrectedPhaseCell_continuousOn_symm W 2 _ constructedA2CircleTwoPhase_isEmbedding

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
