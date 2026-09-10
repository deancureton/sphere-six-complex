module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepCell
public import SphereSixComplex.Prerequisites.Topology.CircleCutChart
public import SphereSixComplex.Prerequisites.Topology.CompactSeparatedRestriction

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric.Construction
open InfiniteA2Toric CuspLocalPhaseAction CuspFilling CuspPeriodExpansion
open CuspStraighteningRetraction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepZeroCarrier (x : Fin 2 → ℝ) : Carrier :=
  fourthPhaseEdgeZeroSweep (circleCutParameter (x 1)) (fun _ ↦ x 0)

public def phaseSweepZeroPoint (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) : actualLocalCuspCentralSubMulAction W :=
  constructedA2CentralCompactMap W ![1, circleCutParameter (x 1)]
    (constructedCentralEdgeZeroPoint W (fun _ ↦ x 0))

public theorem phaseSweepZeroPoint_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    (phaseSweepZeroPoint W x).1.1 = phaseSweepZeroCarrier x := by
  unfold phaseSweepZeroPoint phaseSweepZeroCarrier fourthPhaseEdgeZeroSweep
  dsimp [constructedA2CentralCompactMap, compactPhaseLocalAction,
    constructedCentralEdgeZeroPoint, constructedCentralEdgeZeroLocal]
  apply congrArg (fun g ↦ constructedModel.torusAction g (constructedCentralEdgeZeroCarrier _))
  ext i
  fin_cases i <;>
    simp [compactTorusEmbedding, constructedA2EffectivePhaseSection,
      CuspToricPhaseAction.phaseEmbedding]

public def phaseSweepZeroOrbit (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) : ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  exact Quotient.mk _ (phaseSweepZeroPoint W x)

public theorem phaseSweepZeroPoint_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (phaseSweepZeroPoint W) := by
  unfold phaseSweepZeroPoint constructedA2CentralCompactMap
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply (establishedContinuousTorusAction constructedModel).variable_action
  · apply continuous_compactTorusEmbedding.comp
    apply constructedA2EffectivePhaseSection_continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact circleCutParameter_continuous.comp (continuous_apply 1)
  · change Continuous (fun x : Fin 2 → ℝ ↦ constructedCentralEdgeZeroCarrier (fun _ ↦ x 0))
    exact constructedCentralEdgeZeroCarrier_continuous.comp (continuous_pi fun _ ↦ continuous_apply 0)

public theorem phaseSweepZeroOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (phaseSweepZeroOrbit W) := by
  let _ := actualLocalCuspQuotientAction W
  exact continuous_quotient_mk'.comp (phaseSweepZeroPoint_continuous W)

public theorem phaseSweepZeroCarrier_injOn :
    Set.InjOn phaseSweepZeroCarrier (Metric.ball 0 1) := by
  intro x hx y hy h
  have hb {z : Fin 2 → ℝ} (hz : z ∈ Metric.ball 0 1) (i : Fin 2) :
      z i ∈ Ioo (-1 : ℝ) 1 := by
    have h := (norm_le_pi_norm z i).trans_lt
      (show ‖z‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hz)
    exact abs_lt.mp (by simpa [Real.norm_eq_abs] using h)
  have he {z : Fin 2 → ℝ} (hz : z ∈ Metric.ball 0 1) :
      (fun _ : Fin 1 ↦ z 0) ∈ Metric.ball 0 1 := by
    simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt]
      using hb hz 0
  obtain ⟨hc, hr⟩ := fourthPhaseEdgeZeroSweep_injective _ _ _ _ (he hx) (he hy) h
  have ha := circleCutParameter_injOn (hb hx 1) (hb hy 1) hc
  ext i
  fin_cases i
  · exact congrFun hr 0
  · exact ha

public theorem phaseSweepZeroCarrier_image :
    phaseSweepZeroCarrier '' Metric.ball 0 1 =
      constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
  rw [← fourthPhaseEdgeZeroSweep_image]
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ∀ i, x i ∈ Ioo (-1 : ℝ) 1 := by
      intro i
      have h := (norm_le_pi_norm x i).trans_lt
        (show ‖x‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hx)
      exact abs_lt.mp (by simpa [Real.norm_eq_abs] using h)
    refine ⟨(circleCutParameter (x 1), fun _ ↦ x 0), ⟨circleCutParameter_ne_one (hx' 1), ?_⟩, rfl⟩
    simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt]
      using hx' 0
  · rintro ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩
    obtain ⟨t, ht, htc⟩ := circleCutParameter_surjOn hc
    refine ⟨![x 0, t], ?_, ?_⟩
    · have hx' : -1 < x 0 ∧ x 0 < 1 := by
        simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt] using hx
      simpa [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1),
        Fin.forall_fin_succ, Real.norm_eq_abs, abs_lt, hx'] using ht
    · simp only [phaseSweepZeroCarrier, Matrix.cons_val_one, Matrix.cons_val_zero, htc]
      congr 1
      ext i
      fin_cases i
      rfl

public theorem phaseSweepZeroOrbit_eq_phase
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x y : Fin 2 → ℝ)
    (h : phaseSweepZeroCarrier x = constructedCentralPhaseFaceZeroCarrier y) :
    phaseSweepZeroOrbit W x = constructedCentralPhaseFaceZeroOrbit W y := by
  let _ := actualLocalCuspQuotientAction W
  change Quotient.mk _ (phaseSweepZeroPoint W x) =
    Quotient.mk _ (constructedCentralPhaseFaceZeroPoint W y)
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  rw [phaseSweepZeroPoint_carrier]
  exact h

public theorem phaseSweepZeroOrbit_image
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    phaseSweepZeroOrbit W '' Metric.ball 0 1 =
      constructedCentralPhaseFaceZeroOrbit W '' Metric.ball 0 1 := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hm : phaseSweepZeroCarrier x ∈
        constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
      rw [← phaseSweepZeroCarrier_image]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hm
    exact ⟨y, hy, (phaseSweepZeroOrbit_eq_phase W x y he.symm).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hm : constructedCentralPhaseFaceZeroCarrier y ∈
        phaseSweepZeroCarrier '' Metric.ball 0 1 := by
      rw [phaseSweepZeroCarrier_image]
      exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx, he⟩ := hm
    exact ⟨x, hx, phaseSweepZeroOrbit_eq_phase W x y he⟩

public theorem phaseSweepZeroOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (phaseSweepZeroOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  have hm (z : Fin 2 → ℝ) (hz : z ∈ Metric.ball 0 1) :
      ∃ w ∈ Metric.ball 0 1,
        phaseSweepZeroCarrier z = constructedCentralPhaseFaceZeroCarrier w := by
    have hh : phaseSweepZeroCarrier z ∈
        constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
      rw [← phaseSweepZeroCarrier_image]
      exact ⟨z, hz, rfl⟩
    obtain ⟨w, hw, he⟩ := hh
    exact ⟨w, hw, he.symm⟩
  obtain ⟨a, ha, hea⟩ := hm x hx
  obtain ⟨b, hb, heb⟩ := hm y hy
  have hab : a = b := constructedCentralPhaseFaceZeroOrbit_injOn W ha hb
    ((phaseSweepZeroOrbit_eq_phase W x a hea).symm.trans
      (hxy.trans (phaseSweepZeroOrbit_eq_phase W y b heb)))
  apply phaseSweepZeroCarrier_injOn hx hy
  rw [hea, heb, hab]

public theorem fourthPhaseEdgeZeroSweep_one (x : Fin 1 → ℝ) :
    fourthPhaseEdgeZeroSweep 1 x = constructedCentralEdgeZeroCarrier x := by
  by_cases h : x 0 ≤ 0
  · rw [fourthPhaseEdgeZeroSweep_lower _ _ h]
    simp [constructedCentralEdgeZeroCarrier, h, constructedCentralEdgeZeroLowerBranch]
  · rw [fourthPhaseEdgeZeroSweep_upper _ _ h]
    simp [constructedCentralEdgeZeroCarrier, h, constructedCentralEdgeZeroUpperBranch]

public theorem fourthPhaseEdgeZeroSweep_endpoint (c : Circle) (r : ℝ)
    (hr : r = -1 ∨ r = 1) :
    fourthPhaseEdgeZeroSweep c (fun _ ↦ r) = constructedCentralEdgeZeroCarrier (fun _ ↦ r) := by
  rcases hr with rfl | rfl
  · rw [fourthPhaseEdgeZeroSweep_lower _ _ (by norm_num)]
    simp [constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroLowerBranch]
  · rw [fourthPhaseEdgeZeroSweep_upper _ _ (by norm_num)]
    simp [constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroUpperBranch]

public theorem phaseSweepZeroCarrier_boundary (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    phaseSweepZeroCarrier x = constructedCentralEdgeZeroCarrier (fun _ ↦ x 0) := by
  have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hb (i : Fin 2) : |x i| ≤ 1 := by
    simpa [Real.norm_eq_abs, hn] using norm_le_pi_norm x i
  have he : x 0 = -1 ∨ x 0 = 1 ∨ x 1 = -1 ∨ x 1 = 1 := by
    by_contra h
    push Not at h
    have hlt : ‖x‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr (by
      intro i
      fin_cases i
      · rw [Real.norm_eq_abs, abs_lt]
        have hh := abs_le.mp (hb 0)
        exact ⟨lt_of_le_of_ne hh.1 h.1.symm, lt_of_le_of_ne hh.2 h.2.1⟩
      · rw [Real.norm_eq_abs, abs_lt]
        have hh := abs_le.mp (hb 1)
        exact ⟨lt_of_le_of_ne hh.1 h.2.2.1.symm, lt_of_le_of_ne hh.2 h.2.2.2⟩)
    linarith
  rcases he with h | h | h | h
  · exact fourthPhaseEdgeZeroSweep_endpoint _ _ (Or.inl h)
  · exact fourthPhaseEdgeZeroSweep_endpoint _ _ (Or.inr h)
  · unfold phaseSweepZeroCarrier
    have hc : circleCutParameter (x 1) = 1 := by
      rw [h, show (-1 : ℝ) = 2 * 0 - 1 by ring, circleCutParameter_eq_turn]
      simp
    rw [hc, fourthPhaseEdgeZeroSweep_one]
  · unfold phaseSweepZeroCarrier
    have hc : circleCutParameter (x 1) = 1 := by
      rw [h, show (1 : ℝ) = 2 * 1 - 1 by ring, circleCutParameter_eq_turn]
      simp
    rw [hc, fourthPhaseEdgeZeroSweep_one]

public theorem phaseSweepZeroOrbit_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    phaseSweepZeroOrbit W x = constructedCentralEdgeZeroOrbit W (fun _ ↦ x 0) := by
  let _ := actualLocalCuspQuotientAction W
  change Quotient.mk _ (phaseSweepZeroPoint W x) =
    Quotient.mk _ (constructedCentralEdgeZeroPoint W (fun _ ↦ x 0))
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  rw [phaseSweepZeroPoint_carrier]
  exact phaseSweepZeroCarrier_boundary x hx

public theorem phaseSweepZeroOrbit_closedImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    phaseSweepZeroOrbit W '' Metric.closedBall 0 1 =
      constructedCentralPhaseFaceZeroOrbit W '' Metric.closedBall 0 1 := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  have hcl : closure (Metric.ball (0 : Fin 2 → ℝ) 1) = Metric.closedBall 0 1 :=
    closure_ball 0 one_ne_zero
  have hc : IsCompact (closure (Metric.ball (0 : Fin 2 → ℝ) 1)) := by
    rw [hcl]
    exact isCompact_closedBall 0 1
  have hnew := image_closure_of_isCompact hc (phaseSweepZeroOrbit_continuous W).continuousOn
  have hold := image_closure_of_isCompact hc
    (hcl ▸ constructedCentralPhaseFaceZeroOrbit_continuousOn_closedBall W)
  rw [hcl] at hnew hold
  rw [hnew, hold, phaseSweepZeroOrbit_image]

public theorem phaseSweepZeroOrbit_boundary_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    phaseSweepZeroOrbit W x ∈ constructedCentralOneSkeleton W := by
  rw [phaseSweepZeroOrbit_boundary W x hx]
  right
  apply Set.mem_iUnion.mpr
  refine ⟨0, (fun _ ↦ x 0), ?_, rfl⟩
  have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hb : |x 0| ≤ 1 := by simpa [Real.norm_eq_abs, hn] using norm_le_pi_norm x 0
  simpa [Metric.mem_closedBall, dist_zero_right, Pi.norm_def, Real.norm_eq_abs] using hb

public theorem phaseSweepZeroOrbit_boundary_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Disjoint (phaseSweepZeroOrbit W '' (Metric.closedBall 0 1 \ Metric.ball 0 1))
      (phaseSweepZeroOrbit W '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, ⟨hx, hxb⟩, rfl⟩ hp
  have hxs : x ∈ Metric.sphere 0 1 := by
    simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere,
      dist_zero_right, not_lt] at hx hxb ⊢
    exact le_antisymm hx hxb
  rw [phaseSweepZeroOrbit_image] at hp
  exact Set.disjoint_left.mp (constructedCentralPhaseTwoCell_oneSkeleton_disjoint W 0)
    hp (phaseSweepZeroOrbit_boundary_oneSkeleton W x hxs)

public theorem phaseSweepZeroOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Topology.IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (phaseSweepZeroOrbit W)) := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact isEmbedding_restrict_compact_separated
    (phaseSweepZeroOrbit W) (Metric.ball 0 1) (Metric.closedBall 0 1)
    (isCompact_closedBall 0 1) Metric.ball_subset_closedBall
    (phaseSweepZeroOrbit_continuous W).continuousOn
    (phaseSweepZeroOrbit_injOn W) (phaseSweepZeroOrbit_boundary_disjoint W)

public def phaseSweepZeroCell (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (phaseSweepZeroOrbit W) (Metric.ball 0 1)
    (phaseSweepZeroOrbit_injOn W)

public theorem phaseSweepZeroCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (phaseSweepZeroCell W).symm (phaseSweepZeroCell W).target := by
  let e := phaseSweepZeroCell W
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (phaseSweepZeroOrbit_isEmbedding W).continuous_iff.mpr
    have he : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (phaseSweepZeroOrbit W) ∘ lift =
        (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [he]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hlift

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
