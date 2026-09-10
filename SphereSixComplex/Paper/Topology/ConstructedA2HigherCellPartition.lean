module

public import SphereSixComplex.Paper.Topology.ConstructedA2HigherCells

@[expose] public section

noncomputable section
open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2CorrectedPositiveTwoOrbit_corrected_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1) :
    constructedA2CorrectedPositiveTwoOrbit W x.1 =
      (constructedA2CorrectedSingletonProductHomeomorph W (x, 1)).1 := by
  rw [constructedA2CorrectedPositiveTwoOrbit_ball_formula]
  change (constructedA2ActualSingletonBallPhaseHomeomorph W (x, _)).1 =
    (constructedA2ActualSingletonBallPhaseHomeomorph W (x, _ * 1)).1
  rw [mul_one]

public theorem constructedA2CorrectedPhaseOrbit_relativePhase_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (m n : ℕ) (phase : (Fin m → ℝ) → Fin 2 → Circle) (phase' : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin (2 + m) → ℝ) 1)
    (y : Metric.ball (0 : Fin (2 + n) → ℝ) 1)
    (h : constructedA2CorrectedPhaseOrbit W m phase x.1 =
      constructedA2CorrectedPhaseOrbit W n phase' y.1) :
    phase (SupNormBall.prodHomeomorph 2 m x).2.1 =
      phase' (SupNormBall.prodHomeomorph 2 n y).2.1 := by
  rw [constructedA2CorrectedPhaseOrbit_ball_formula,
    constructedA2CorrectedPhaseOrbit_ball_formula] at h
  have hp := (constructedA2CorrectedSingletonProductHomeomorph W).injective (Subtype.ext h)
  exact congrArg Prod.snd hp

public theorem constructedA2CorrectedPositiveTwo_relativePhase_eq_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1)
    (y : Metric.ball (0 : Fin (2 + n) → ℝ) 1)
    (h : constructedA2CorrectedPositiveTwoOrbit W x.1 =
      constructedA2CorrectedPhaseOrbit W n phase y.1) :
    phase (SupNormBall.prodHomeomorph 2 n y).2.1 = 1 := by
  rw [constructedA2CorrectedPositiveTwoOrbit_corrected_formula,
    constructedA2CorrectedPhaseOrbit_ball_formula] at h
  have hp := (constructedA2CorrectedSingletonProductHomeomorph W).injective (Subtype.ext h)
  exact (congrArg Prod.snd hp).symm

public theorem constructedCircleBallCell_ne_one {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.ball 0 1) : CircleCell.ballParam x ≠ 1 :=
  CircleCell.param_ne_one (SupNormBall.oneHomeomorphIoo ⟨x, hx⟩).property

public theorem constructedA2CircleOnePhase_ne_one {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.ball 0 1) (i : Fin 2) : constructedA2CircleOnePhase i x ≠ 1 := by
  intro h
  have hi := congrFun h i
  fin_cases i <;>
    simp [constructedA2CircleOnePhase] at hi <;>
    exact constructedCircleBallCell_ne_one hx hi

public theorem constructedA2CircleTwoPhase_apply_ne_one {x : Fin 2 → ℝ}
    (hx : x ∈ Metric.ball 0 1) (i : Fin 2) : constructedA2CircleTwoPhase x i ≠ 1 := by
  have hn : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hi : |x i| < 1 := (norm_le_pi_norm x i).trans_lt hn
  exact CircleCell.param_ne_one (abs_lt.mp hi)

public theorem constructedA2CorrectedPositiveTwo_three_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    Disjoint (constructedA2CorrectedPositiveTwoOrbit W '' Metric.ball 0 1)
      (constructedA2CorrectedThreeOrbit W i '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := constructedA2CorrectedPositiveTwo_relativePhase_eq_one W 1 _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  exact constructedA2CircleOnePhase_ne_one (SupNormBall.prodHomeomorph 2 1 ⟨y, hy⟩).2.property i h

public theorem constructedA2CorrectedPositiveTwo_four_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Disjoint (constructedA2CorrectedPositiveTwoOrbit W '' Metric.ball 0 1)
      (constructedA2CorrectedFourOrbit W '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := constructedA2CorrectedPositiveTwo_relativePhase_eq_one W 2 _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  exact constructedA2CircleTwoPhase_apply_ne_one
    (SupNormBall.prodHomeomorph 2 2 ⟨y, hy⟩).2.property 0 (congrFun h 0)

public theorem constructedA2CorrectedThreeOrbit_pairwiseDisjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Set.univ : Set (Fin 2)).PairwiseDisjoint
      (fun i ↦ constructedA2CorrectedThreeOrbit W i '' Metric.ball 0 1) := by
  intro i _ j _ hij
  change Disjoint _ _
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := constructedA2CorrectedPhaseOrbit_relativePhase_eq W 1 1 _ _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  have hi := congrFun h i
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | dsimp [constructedA2CircleOnePhase] at hi
      exact constructedCircleBallCell_ne_one
        (SupNormBall.prodHomeomorph 2 1 ⟨x, hx⟩).2.property hi

public theorem constructedA2CorrectedThree_four_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    Disjoint (constructedA2CorrectedThreeOrbit W i '' Metric.ball 0 1)
      (constructedA2CorrectedFourOrbit W '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have h := constructedA2CorrectedPhaseOrbit_relativePhase_eq W 1 2 _ _
    ⟨x, hx⟩ ⟨y, hy⟩ (hxq.trans hyq.symm)
  fin_cases i
  · have hi := congrFun h 1
    dsimp [constructedA2CircleOnePhase] at hi
    exact constructedA2CircleTwoPhase_apply_ne_one
      (SupNormBall.prodHomeomorph 2 2 ⟨y, hy⟩).2.property 1 hi.symm
  · have hi := congrFun h 0
    dsimp [constructedA2CircleOnePhase] at hi
    exact constructedA2CircleTwoPhase_apply_ne_one
      (SupNormBall.prodHomeomorph 2 2 ⟨y, hy⟩).2.property 0 hi.symm

public theorem constructedA2CorrectedPositiveTwoOrbit_mem_singleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    constructedA2CorrectedPositiveTwoOrbit W x ∈ constructedA2ActualSingletonStratum W := by
  rw [constructedA2CorrectedPositiveTwoOrbit_corrected_formula W ⟨x, hx⟩]
  exact (constructedA2CorrectedSingletonProductHomeomorph W (⟨x, hx⟩, 1)).property

public theorem constructedA2CorrectedPhaseOrbit_mem_singleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    {x : Fin (2 + n) → ℝ} (hx : x ∈ Metric.ball 0 1) :
    constructedA2CorrectedPhaseOrbit W n phase x ∈ constructedA2ActualSingletonStratum W := by
  rw [constructedA2CorrectedPhaseOrbit_ball_formula W n phase ⟨x, hx⟩]
  exact (constructedA2CorrectedSingletonProductHomeomorph W _).property

public theorem constructedA2ActualSingleton_not_of_support_ge_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (hp : 2 ≤ (componentSupport constructedModel (p.1.1 : constructedModel.Carrier)).ncard) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p ∉ constructedA2ActualSingletonStratum W := by
  rintro ⟨q, hq, hcard⟩
  have hrel := Quotient.exact hq
  have hn := constructedA2ActualCentralOrbitRel_componentSupport_ncard_eq W q p hrel
  rw [hcard] at hn
  omega

public theorem constructedCircleCell_surjOn_closed :
    Set.SurjOn CircleCell.param (Icc (-1 : ℝ) 1) Set.univ := by
  intro z _
  by_cases hz : z = 1
  · exact ⟨-1, by norm_num, by simp [hz]⟩
  · obtain ⟨t, ht, heq⟩ := CircleCell.surjOn_param hz
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, heq⟩

public theorem constructedA2CircleTwoPhase_surjOn_closed :
    Set.SurjOn constructedA2CircleTwoPhase (Metric.closedBall 0 1) Set.univ := by
  intro k _
  choose t ht heq using fun j : Fin 2 ↦ constructedCircleCell_surjOn_closed (Set.mem_univ (k j))
  refine ⟨t, ?_, funext heq⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro j
  exact abs_le.mpr (ht j)

public theorem constructedA2CorrectedPhaseOrbit_append_ball_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (x : Metric.ball (0 : Fin 2 → ℝ) 1) (y : Fin n → ℝ) :
    constructedA2CorrectedPhaseOrbit W n phase ((Fin.appendHomeomorph (X := ℝ) 2 n) (x.1, y)) =
      (constructedA2CorrectedSingletonProductHomeomorph W (x, phase y)).1 := by
  unfold constructedA2CorrectedPhaseOrbit
  rw [(Fin.appendHomeomorph (X := ℝ) 2 n).symm_apply_apply]
  dsimp only
  rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
    W.localWitness.radius_pos 0 x.1 (Metric.ball_subset_closedBall x.property)]
  rfl

public theorem constructedA2ActualSingleton_subset_closedFour
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedA2ActualSingletonStratum W ⊆
      constructedA2CorrectedFourOrbit W '' Metric.closedBall 0 1 := by
  intro q hq
  let p := (constructedA2CorrectedSingletonProductHomeomorph W).symm ⟨q, hq⟩
  obtain ⟨t, ht, hphase⟩ := constructedA2CircleTwoPhase_surjOn_closed (Set.mem_univ p.2)
  refine ⟨(Fin.appendHomeomorph (X := ℝ) 2 2) (p.1.1, t), ?_, ?_⟩
  · exact (constructedAppend_mem_closedBall 2 2 (p.1.1, t)).mpr
      ⟨Metric.ball_subset_closedBall p.1.property, ht⟩
  · change constructedA2CorrectedPhaseOrbit W 2 constructedA2CircleTwoPhase _ = q
    rw [constructedA2CorrectedPhaseOrbit_append_ball_formula, hphase]
    exact congrArg Subtype.val ((constructedA2CorrectedSingletonProductHomeomorph W).apply_symm_apply ⟨q, hq⟩)

public theorem constructedA2BoundaryTwoSkeleton_union_closedFour
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralBoundaryTwoSkeleton W ∪
      (constructedA2CorrectedFourOrbit W '' Metric.closedBall 0 1) = Set.univ := by
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
      apply constructedA2ActualSingleton_subset_closedFour W
      exact ⟨p, rfl, by omega⟩

end SphereSixComplex.Geometry.InfiniteA2Toric

end
