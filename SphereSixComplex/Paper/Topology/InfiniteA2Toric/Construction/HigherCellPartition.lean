module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HigherCells

@[expose] public section

noncomputable section
open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}
namespace Construction


public theorem correctedPositiveTwoOrbit_corrected_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1) :
    correctedPositiveTwoOrbit W x.1 =
      (correctedSingletonProductHomeomorph W (x, 1)).1 := by
  rw [correctedPositiveTwoOrbit_ball_formula]
  change (actualSingletonBallPhaseHomeomorph W (x, _)).1 =
    (actualSingletonBallPhaseHomeomorph W (x, _ * 1)).1
  rw [mul_one]

public theorem correctedPhaseOrbit_relativePhase_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (m n : ℕ) (phase : (Fin m → ℝ) → Fin 2 → Circle) (phase' : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin (2 + m) → ℝ) 1)
    (y : Metric.ball (0 : Fin (2 + n) → ℝ) 1)
    (h : correctedPhaseOrbit W m phase x.1 =
      correctedPhaseOrbit W n phase' y.1) :
    phase (SupNormBall.prodHomeomorph 2 m x).2.1 =
      phase' (SupNormBall.prodHomeomorph 2 n y).2.1 := by
  rw [correctedPhaseOrbit_ball_formula,
    correctedPhaseOrbit_ball_formula] at h
  have hp := (correctedSingletonProductHomeomorph W).injective (Subtype.ext h)
  exact congrArg Prod.snd hp

public theorem correctedPositiveTwo_relativePhase_eq_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1)
    (y : Metric.ball (0 : Fin (2 + n) → ℝ) 1)
    (h : correctedPositiveTwoOrbit W x.1 =
      correctedPhaseOrbit W n phase y.1) :
    phase (SupNormBall.prodHomeomorph 2 n y).2.1 = 1 := by
  rw [correctedPositiveTwoOrbit_corrected_formula,
    correctedPhaseOrbit_ball_formula] at h
  have hp := (correctedSingletonProductHomeomorph W).injective (Subtype.ext h)
  exact (congrArg Prod.snd hp).symm
end Construction


public theorem constructedCircleBallCell_ne_one {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.ball 0 1) : CircleCell.ballParam x ≠ 1 :=
  CircleCell.param_ne_one (SupNormBall.oneHomeomorphIoo ⟨x, hx⟩).property
namespace Construction


public theorem circleOnePhase_ne_one {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.ball 0 1) (i : Fin 2) : CircleCell.onePhase i x ≠ 1 := by
  intro h
  have hi := congrFun h i
  fin_cases i <;>
    simp [CircleCell.onePhase] at hi <;>
    exact constructedCircleBallCell_ne_one hx hi

public theorem circleTwoPhase_apply_ne_one {x : Fin 2 → ℝ}
    (hx : x ∈ Metric.ball 0 1) (i : Fin 2) : CircleCell.twoPhase x i ≠ 1 := by
  have hn : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hi : |x i| < 1 := (norm_le_pi_norm x i).trans_lt hn
  exact CircleCell.param_ne_one (abs_lt.mp hi)

public theorem correctedPositiveTwo_three_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    Disjoint (correctedPositiveTwoOrbit W '' Metric.ball 0 1)
      (correctedThreeOrbit W i '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := correctedPositiveTwo_relativePhase_eq_one W 1 _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  exact circleOnePhase_ne_one (SupNormBall.prodHomeomorph 2 1 ⟨y, hy⟩).2.property i h

public theorem correctedPositiveTwo_four_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Disjoint (correctedPositiveTwoOrbit W '' Metric.ball 0 1)
      (correctedFourOrbit W '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := correctedPositiveTwo_relativePhase_eq_one W 2 _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  exact circleTwoPhase_apply_ne_one
    (SupNormBall.prodHomeomorph 2 2 ⟨y, hy⟩).2.property 0 (congrFun h 0)

public theorem correctedThreeOrbit_pairwiseDisjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Set.univ : Set (Fin 2)).PairwiseDisjoint
      (fun i ↦ correctedThreeOrbit W i '' Metric.ball 0 1) := by
  intro i _ j _ hij
  change Disjoint _ _
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := correctedPhaseOrbit_relativePhase_eq W 1 1 _ _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  have hi := congrFun h i
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | dsimp [CircleCell.onePhase] at hi
      exact constructedCircleBallCell_ne_one
        (SupNormBall.prodHomeomorph 2 1 ⟨x, hx⟩).2.property hi

public theorem correctedThree_four_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    Disjoint (correctedThreeOrbit W i '' Metric.ball 0 1)
      (correctedFourOrbit W '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := correctedPhaseOrbit_relativePhase_eq W 1 2 _ _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  fin_cases i
  · have hi := congrFun h 1
    dsimp [CircleCell.onePhase] at hi
    exact circleTwoPhase_apply_ne_one
      (SupNormBall.prodHomeomorph 2 2 ⟨y, hy⟩).2.property 1 hi.symm
  · have hi := congrFun h 0
    dsimp [CircleCell.onePhase] at hi
    exact circleTwoPhase_apply_ne_one
      (SupNormBall.prodHomeomorph 2 2 ⟨y, hy⟩).2.property 0 hi.symm

public theorem correctedPositiveTwoOrbit_mem_singleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    correctedPositiveTwoOrbit W x ∈ actualSingletonStratum W := by
  rw [correctedPositiveTwoOrbit_corrected_formula W ⟨x, hx⟩]
  exact (correctedSingletonProductHomeomorph W (⟨x, hx⟩, 1)).property

public theorem correctedPhaseOrbit_mem_singleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    {x : Fin (2 + n) → ℝ} (hx : x ∈ Metric.ball 0 1) :
    correctedPhaseOrbit W n phase x ∈ actualSingletonStratum W := by
  rw [correctedPhaseOrbit_ball_formula W n phase ⟨x, hx⟩]
  exact (correctedSingletonProductHomeomorph W _).property

public theorem actualSingleton_not_of_support_ge_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (hp : 2 ≤ (componentSupport constructedModel (p.1.1 : constructedModel.Carrier)).ncard) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p ∉ actualSingletonStratum W := by
  rintro ⟨q, hq, hcard⟩
  have hrel := Quotient.exact hq
  have hn := actualCentralOrbitRel_componentSupport_ncard_eq W q p hrel
  rw [hcard] at hn
  omega
end Construction


public theorem constructedCircleCell_surjOn_closed :
    Set.SurjOn CircleCell.param (Icc (-1 : ℝ) 1) Set.univ := by
  intro z _
  by_cases hz : z = 1
  · exact ⟨-1, by norm_num, by simp [hz]⟩
  · obtain ⟨t, ht, heq⟩ := CircleCell.surjOn_param hz
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, heq⟩
namespace Construction


public theorem circleTwoPhase_surjOn_closed :
    Set.SurjOn CircleCell.twoPhase (Metric.closedBall 0 1) Set.univ := by
  intro k _
  choose t ht heq using fun j : Fin 2 ↦ constructedCircleCell_surjOn_closed (Set.mem_univ (k j))
  refine ⟨t, ?_, funext heq⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro j
  exact abs_le.mpr (ht j)

public theorem correctedPhaseOrbit_append_ball_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1) (y : Fin n → ℝ) :
    correctedPhaseOrbit W n phase ((Fin.appendHomeomorph (X := ℝ) 2 n) (x.1, y)) =
      (correctedSingletonProductHomeomorph W (x, phase y)).1 := by
  unfold correctedPhaseOrbit
  rw [(Fin.appendHomeomorph (X := ℝ) 2 n).symm_apply_apply]
  dsimp only
  rw [correctedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 x.1 (Metric.ball_subset_closedBall x.property)]
  rfl

public theorem actualSingleton_subset_closedFour
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    actualSingletonStratum W ⊆
      correctedFourOrbit W '' Metric.closedBall 0 1 := by
  intro q hq
  let p := (correctedSingletonProductHomeomorph W).symm ⟨q, hq⟩
  obtain ⟨t, ht, hphase⟩ := circleTwoPhase_surjOn_closed (Set.mem_univ p.2)
  refine ⟨(Fin.appendHomeomorph (X := ℝ) 2 2) (p.1.1, t), ?_, ?_⟩
  · exact (SupNormBall.append_mem_closedBall_iff 2 2 (p.1.1, t)).mpr
      ⟨Metric.ball_subset_closedBall p.1.property, ht⟩
  · change correctedPhaseOrbit W 2 CircleCell.twoPhase _ = q
    rw [correctedPhaseOrbit_append_ball_formula, hphase]
    exact congrArg Subtype.val ((correctedSingletonProductHomeomorph W).apply_symm_apply ⟨q, hq⟩)

public theorem boundaryTwoSkeleton_union_closedFour
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralBoundaryTwoSkeleton W ∪
      (correctedFourOrbit W '' Metric.closedBall 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    have hfinite := componentSupport_finite constructedModel (p.1.1 : constructedModel.Carrier)
    have hpos := (Set.ncard_pos hfinite).mpr
      (componentSupport_nonempty_of_t_eq_zero constructedModel p.property)
    by_cases hge : 2 ≤ (componentSupport constructedModel (p.1.1 : constructedModel.Carrier)).ncard
    · exact Or.inl (constructedCentral_support_ge_two_mem_boundaryTwoSkeleton W p hge)
    · apply Or.inr
      apply actualSingleton_subset_closedFour W
      exact ⟨p, rfl, by omega⟩

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
