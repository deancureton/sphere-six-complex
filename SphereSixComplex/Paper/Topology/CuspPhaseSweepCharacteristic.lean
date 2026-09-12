module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepCell
public import SphereSixComplex.Prerequisites.Topology.CircleCutChart
public import SphereSixComplex.Prerequisites.Topology.CompactSeparatedRestriction

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric.Construction
open InfiniteA2Toric CuspLocalPhaseAction CuspFilling CuspPeriodExpansion
open CuspStraighteningRetraction
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepZeroCarrier (x : Fin 2 → ℝ) : Carrier :=
  fourthPhaseEdgeZeroSweep (circleCutParameter (x 1)) (fun _ ↦ x 0)

public def phaseSweepZeroPoint (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) : actualLocalCuspCentralSubMulAction W :=
  centralCompactMap W ![1, circleCutParameter (x 1)]
    (constructedCentralEdgeZeroPoint W (fun _ ↦ x 0))

public theorem phaseSweepZeroPoint_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    (phaseSweepZeroPoint W x).1.1 = phaseSweepZeroCarrier x := by
  unfold phaseSweepZeroPoint phaseSweepZeroCarrier fourthPhaseEdgeZeroSweep
  dsimp [centralCompactMap, compactPhaseLocalAction,
    constructedCentralEdgeZeroPoint, constructedCentralEdgeZeroLocal]
  apply congrArg (fun g ↦ constructedModel.torusAction g (constructedCentralEdgeZeroCarrier _))
  ext i
  fin_cases i <;>
    simp [compactTorusEmbedding, effectivePhaseSection,
      CuspToricPhaseAction.phaseEmbedding]


public theorem phaseSweepZeroPoint_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (phaseSweepZeroPoint W) := by
  unfold phaseSweepZeroPoint centralCompactMap
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hg : Continuous (fun x : Fin 2 → ℝ ↦ compactTorusEmbedding
      (effectivePhaseSection ![1, circleCutParameter (x 1)])) := by
    apply continuous_compactTorusEmbedding.comp
    apply continuous_effectivePhaseSection.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact circleCutParameter_continuous.comp (continuous_apply 1)
  have hp : Continuous (fun x : Fin 2 → ℝ ↦
      constructedCentralEdgeZeroCarrier (fun _ ↦ x 0)) :=
    constructedCentralEdgeZeroCarrier_continuous.comp (continuous_pi fun _ ↦ continuous_apply 0)
  exact Continuous.comp
    (f := fun x : Fin 2 → ℝ ↦
      (compactTorusEmbedding (effectivePhaseSection ![1, circleCutParameter (x 1)]),
        constructedCentralEdgeZeroCarrier (fun _ ↦ x 0)))
    (g := fun z : DenseTorus × constructedModel.Carrier ↦ constructedModel.torusAction z.1 z.2)
    (continuous_torusAction constructedModel) (hg.prodMk hp)


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








end SphereSixComplex.Geometry.CuspCollar
