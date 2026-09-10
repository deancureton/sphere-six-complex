module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCompactPhaseCorrection
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

public theorem centralPhaseDiskComplex_surjective : Function.Surjective centralPhaseDiskComplex := by
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by simp [centralPhaseDiskComplex, hz]⟩
  let y : Fin 2 → ℝ := ![z.re, z.im]
  have hy : centralPhaseLinearComplex y = z := by
    apply Complex.ext <;> simp [centralPhaseLinearComplex, y]
  have hy0 : y ≠ 0 := by
    intro h
    apply hz
    rw [← hy, h]
    simp [centralPhaseLinearComplex]
  let a := ‖z‖ / ‖y‖
  have ha : 0 < a := div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hy0)
  have hx : a • y ≠ 0 := smul_ne_zero ha.ne' hy0
  have hlinear : centralPhaseLinearComplex (a • y) = (a : ℂ) * z := by
    apply Complex.ext <;> simp [centralPhaseLinearComplex, y, Complex.mul_re, Complex.mul_im]
  refine ⟨a • y, ?_⟩
  rw [centralPhaseDiskComplex, ite_eq_right hx, hlinear, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hay : a * ‖y‖ = ‖z‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy0)
  rw [hay]
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hzc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  push_cast
  field_simp

public theorem exists_positiveRealPart_neg_sq_root (z : ℂ)
    (hz : ¬(z.im = 0 ∧ 0 ≤ z.re)) :
    ∃ w : ℂ, 0 < w.re ∧ -(w ^ 2) = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-z) (show 0 < 2 by decide)
  have hwre : w.re ≠ 0 := by
    intro hzero
    apply hz
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [pow_two, Complex.mul_re, Complex.mul_im, hzero] at hre him
    exact ⟨him, by nlinarith [sq_nonneg w.im]⟩
  rcases lt_or_gt_of_ne hwre with h | h
  · refine ⟨-w, by simpa using h, ?_⟩
    rw [neg_sq, hw, neg_neg]
  · exact ⟨w, h, by rw [hw, neg_neg]⟩

public theorem norm_cayleyInverse_lt_one (w : ℂ) (hw : 0 < w.re) :
    ‖(w - 1) / (w + 1)‖ < 1 := by
  have hden : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have hs : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  nlinarith [norm_nonneg (w - 1), norm_nonneg (w + 1)]

public theorem re_cayleyInverse_nonpos (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ((w - 1) / (w + 1)).re ≤ 0 := by
  rw [Complex.div_re, ← add_div]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hs : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg w]
    simp only [Complex.normSq_apply] at hs
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    nlinarith
  · exact Complex.normSq_nonneg _

public theorem exists_centralPhaseDisk_of_norm_lt_one_re_nonpos
    (z : ℂ) (hz : ‖z‖ < 1) (hzre : z.re ≤ 0) :
    ∃ x : Fin 2 → ℝ, x ∈ Metric.ball 0 1 ∧ x 0 ≤ 0 ∧ centralPhaseDiskComplex x = z := by
  obtain ⟨x, hx⟩ := centralPhaseDiskComplex_surjective z
  refine ⟨x, ?_, ?_, hx⟩
  · rw [Metric.mem_ball, dist_zero_right, ← norm_centralPhaseDiskComplex, hx]
    exact hz
  · by_cases hx0 : x = 0
    · simp [hx0]
    have hlinear : centralPhaseLinearComplex x ≠ 0 := by
      intro h
      apply hx0
      funext i
      fin_cases i
      · simpa [centralPhaseLinearComplex] using congrArg Complex.re h
      · simpa [centralPhaseLinearComplex] using congrArg Complex.im h
    have hscale : 0 < ‖x‖ / ‖centralPhaseLinearComplex x‖ :=
      div_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hlinear)
    have hre := congrArg Complex.re hx
    simp [centralPhaseDiskComplex, hx0, centralPhaseLinearComplex, Complex.mul_re] at hre
    simp only [centralPhaseLinearComplex] at hscale
    nlinarith

/-- Every point of the coordinate axis off its positive-real cut belongs to the existing
open phase two-cell. -/
public theorem lowerAxisZero_mem_phaseFace_of_not_nonnegReal
    (z : ℂ) (hcut : ¬(z.im = 0 ∧ 0 ≤ z.re)) :
    inclusion (false, 0) (lowerAxisZero z) ∈
      constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
  obtain ⟨w, hwre, hw⟩ := exists_positiveRealPart_neg_sq_root z hcut
  have hz : z ≠ 0 := by rintro rfl; simp at hcut
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwre
  have hplus : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  let d := (w - 1) / (w + 1)
  obtain ⟨x, hxd⟩ := centralPhaseDiskComplex_surjective d
  have hxball : x ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right, ← norm_centralPhaseDiskComplex, hxd]
    exact norm_cayleyInverse_lt_one w hwre
  have hratio : (1 + d) / (1 - d) = w := by
    dsimp [d]
    field_simp
    ring
  refine ⟨x, hxball, ?_⟩
  by_cases hxre : x 0 ≤ 0
  · rw [constructedCentralPhaseFaceZeroCarrier, ite_eq_left hxre,
      centralPhaseDiskLowerCoordinate, hxd, hratio, hw]
  · have hratio' : (1 - d) / (1 + d) = w⁻¹ := by
      dsimp [d]
      field_simp [hw0]
      ring
    have hupper : -(w⁻¹ ^ 2) = z⁻¹ := by rw [← hw]; simp
    rw [constructedCentralPhaseFaceZeroCarrier, ite_eq_right hxre,
      centralPhaseDiskUpperCoordinate, hxd, hratio', hupper]
    exact (inclusion_lowerAxisZero_eq_upperAxisTwo 0 z hz).symm

public theorem lowerAxisZero_mem_edgeZero_of_nonnegReal (r : ℝ) (hr : 0 ≤ r) :
    inclusion (false, 0) (lowerAxisZero (r : ℂ)) ∈
      constructedCentralEdgeZeroCarrier '' Metric.closedBall 0 1 := by
  by_cases hr1 : r ≤ 1
  · let x : Fin 1 → ℝ := fun _ ↦ r - 1
    have hx : x ∈ Metric.closedBall 0 1 := by
      have hb : -1 ≤ r - 1 ∧ r - 1 ≤ 1 := by constructor <;> linarith
      simpa [x, Metric.mem_closedBall, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_le]
        using hb
    refine ⟨x, hx, ?_⟩
    have hx0 : x 0 ≤ 0 := by dsimp [x]; linarith
    simp [constructedCentralEdgeZeroCarrier, hx0, constructedCentralEdgeZeroLowerBranch, x]
  · have hrpos : 0 < r := lt_trans zero_lt_one (lt_of_not_ge hr1)
    have hri0 : 0 < r⁻¹ := inv_pos.mpr hrpos
    have hri1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_of_not_ge hr1)
    let x : Fin 1 → ℝ := fun _ ↦ 1 - r⁻¹
    have hx : x ∈ Metric.closedBall 0 1 := by
      have hb : -1 ≤ 1 - r⁻¹ ∧ 1 - r⁻¹ ≤ 1 := by constructor <;> linarith
      simpa [x, Metric.mem_closedBall, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_le]
        using hb
    refine ⟨x, hx, ?_⟩
    have hx0 : ¬x 0 ≤ 0 := by dsimp [x]; linarith
    simp only [constructedCentralEdgeZeroCarrier, hx0, ↓reduceIte,
      constructedCentralEdgeZeroUpperBranch, x, sub_sub_cancel]
    simpa using (inclusion_lowerAxisZero_eq_upperAxisTwo 0 (r : ℂ)
      (by exact_mod_cast hrpos.ne')).symm

/-- The existing one-cell and phase two-cell cover the entire lower coordinate axis. -/
public theorem lowerAxisZero_mem_edge_or_phaseFace (z : ℂ) :
    inclusion (false, 0) (lowerAxisZero z) ∈
      (constructedCentralEdgeZeroCarrier '' Metric.closedBall 0 1) ∪
        (constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1) := by
  by_cases hz : z.im = 0 ∧ 0 ≤ z.re
  · apply Or.inl
    have heq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz.1]
    rw [← heq]
    exact lowerAxisZero_mem_edgeZero_of_nonnegReal z.re hz.2
  · exact Or.inr (lowerAxisZero_mem_phaseFace_of_not_nonnegReal z hz)

/-- The same two cells cover the upper chart, including the point at infinity. -/
public theorem upperAxisTwo_mem_edge_or_phaseFace (z : ℂ) :
    inclusion (true, 0) (upperAxisTwo z) ∈
      (constructedCentralEdgeZeroCarrier '' Metric.closedBall 0 1) ∪
        (constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1) := by
  by_cases hz : z = 0
  · apply Or.inl
    refine ⟨fun _ ↦ 1, ?_, ?_⟩
    · simp [Metric.mem_closedBall, dist_zero_right, Pi.norm_def]
    · simp [constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroUpperBranch, hz]
  · have heq := inclusion_lowerAxisZero_eq_upperAxisTwo 0 z⁻¹ (inv_ne_zero hz)
    rw [inv_inv] at heq
    rw [← heq]
    exact lowerAxisZero_mem_edge_or_phaseFace z⁻¹

public theorem a2CyclicCarrier_constructedCentralEdgeZeroCarrier (x : Fin 1 → ℝ) :
    a2CyclicCarrier (constructedCentralEdgeZeroCarrier x) =
      constructedCentralEdgeOneCarrier x := by
  by_cases hx : x 0 ≤ 0
  · simp only [constructedCentralEdgeZeroCarrier, constructedCentralEdgeOneCarrier,
      hx, ↓reduceIte, constructedCentralEdgeZeroLowerBranch]
    rw [a2CyclicCarrier_inclusion, a2CyclicChartIndex_lower_zero]
    exact congrArg (inclusion (false, 0)) (a2CyclicRawLower_lowerAxisZero _)
  · simp only [constructedCentralEdgeZeroCarrier, constructedCentralEdgeOneCarrier,
      hx, ↓reduceIte, constructedCentralEdgeZeroUpperBranch]
    rw [a2CyclicCarrier_inclusion, a2CyclicChartIndex_upper_zero]
    exact congrArg (inclusion (true, -e₁)) (a2CyclicRawUpper_upperAxisTwo _)

public theorem a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier (x : Fin 1 → ℝ) :
    a2CyclicCarrier (a2CyclicCarrier (constructedCentralEdgeZeroCarrier x)) =
      constructedCentralEdgeTwoCarrier x := by
  by_cases hx : x 0 ≤ 0
  · simp only [constructedCentralEdgeZeroCarrier, constructedCentralEdgeTwoCarrier,
      hx, ↓reduceIte, constructedCentralEdgeZeroLowerBranch]
    rw [a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion, a2CyclicChartIndex_lower_zero]
    simpa [a2CyclicRaw] using congrArg (inclusion (false, 0))
      (a2CyclicRawLower_sq_lowerAxisZero _)
  · simp only [constructedCentralEdgeZeroCarrier, constructedCentralEdgeTwoCarrier,
      hx, ↓reduceIte, constructedCentralEdgeZeroUpperBranch]
    rw [a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion, a2CyclicChartIndex_sq_upper_zero]
    exact congrArg (inclusion (true, -e₂)) (a2CyclicRawUpper_sq_upperAxisTwo _)

public def constructedCentralEdgeCarrier : Fin 3 → (Fin 1 → ℝ) → Carrier :=
  ![constructedCentralEdgeZeroCarrier, constructedCentralEdgeOneCarrier,
    constructedCentralEdgeTwoCarrier]

public def constructedCentralPhaseFaceCarrier : Fin 3 → (Fin 2 → ℝ) → Carrier :=
  ![constructedCentralPhaseFaceZeroCarrier, constructedCentralPhaseFaceOneCarrier,
    constructedCentralPhaseFaceTwoCarrier]

public theorem lowerSingleAxis_mem_edge_or_phaseFace (j : Fin 3) (z : ℂ) :
    inclusion (false, 0) (singleAxis j z) ∈
      (constructedCentralEdgeCarrier j '' Metric.closedBall 0 1) ∪
        (constructedCentralPhaseFaceCarrier j '' Metric.ball 0 1) := by
  have h := lowerAxisZero_mem_edge_or_phaseFace z
  fin_cases j
  · have heq : singleAxis 0 z = lowerAxisZero z := by
      funext i
      fin_cases i <;> simp [singleAxis, lowerAxisZero]
    simpa [constructedCentralEdgeCarrier, constructedCentralPhaseFaceCarrier, heq] using h
  · rcases h with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
    · refine Or.inl ⟨x, hx, ?_⟩
      have hr := congrArg a2CyclicCarrier heq
      rw [a2CyclicCarrier_constructedCentralEdgeZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicChartIndex_lower_zero] at hr
      simpa [constructedCentralEdgeCarrier, a2CyclicRaw, a2CyclicRawLower_lowerAxisZero] using hr
    · refine Or.inr ⟨x, hx, ?_⟩
      have hr := congrArg a2CyclicCarrier heq
      rw [a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicChartIndex_lower_zero] at hr
      simpa [constructedCentralPhaseFaceCarrier, a2CyclicRaw, a2CyclicRawLower_lowerAxisZero] using hr
  · rcases h with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
    · refine Or.inl ⟨x, hx, ?_⟩
      have hr := congrArg (a2CyclicCarrier ∘ a2CyclicCarrier) heq
      simp only [Function.comp_apply] at hr
      rw [a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
        a2CyclicChartIndex_lower_zero] at hr
      simpa [constructedCentralEdgeCarrier, a2CyclicRaw, a2CyclicRawLower_sq_lowerAxisZero] using hr
    · refine Or.inr ⟨x, hx, ?_⟩
      have hr := congrArg (a2CyclicCarrier ∘ a2CyclicCarrier) heq
      simp only [Function.comp_apply] at hr
      rw [a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
        a2CyclicChartIndex_lower_zero] at hr
      simpa [constructedCentralPhaseFaceCarrier, a2CyclicRaw, a2CyclicRawLower_sq_lowerAxisZero] using hr

public theorem componentSupport_inclusion_eq_zeroCoordinates
    (a : ChartIndex) (z : RawCoordinates) :
    componentSupport constructedModel (inclusion a z) =
      (a2Triangle a.1 a.2) '' {i : Fin 3 | z i = 0} := by
  let _ := chartedSpace
  have hchart : inclusion a z ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self z
  ext v
  constructor
  · intro hv
    have hin : v ∈ Set.range (a2Triangle a.1 a.2) := by
      by_contra hn
      exact Set.disjoint_left.mp (otherCarrierCentralComponent_disjoint_chart a v hn) hv hchart
    obtain ⟨i, rfl⟩ := hin
    refine ⟨i, ?_, rfl⟩
    have hz := (carrierCentralComponent_in_chart a i _ hchart).mp hv
    simpa [toricChart_inclusion, rawToComplexModel] using hz
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a, i, z, rfl, hi, rfl⟩

/-- A point on at least two toric components is a single coordinate-axis point in every
affine chart containing it. -/
public theorem exists_singleAxis_of_componentSupport_ncard_ge_two
    (a : ChartIndex) (z : RawCoordinates)
    (hz : 2 ≤ (componentSupport constructedModel (inclusion a z)).ncard) :
    ∃ j : Fin 3, z = singleAxis j (z j) := by
  by_cases h0 : z 0 = 0 <;> by_cases h1 : z 1 = 0 <;> by_cases h2 : z 2 = 0
  all_goals solve
    | refine ⟨0, ?_⟩; funext i; fin_cases i <;> simp_all [singleAxis]
    | refine ⟨1, ?_⟩; funext i; fin_cases i <;> simp_all [singleAxis]
    | refine ⟨2, ?_⟩; funext i; fin_cases i <;> simp_all [singleAxis]
    | have hs : {i : Fin 3 | z i = 0} = {0} := by
        ext i; fin_cases i <;> simp_all; done
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs,
        Set.image_singleton, Set.ncard_singleton] at hz
      omega
    | have hs : {i : Fin 3 | z i = 0} = {1} := by
        ext i; fin_cases i <;> simp_all; done
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs,
        Set.image_singleton, Set.ncard_singleton] at hz
      omega
    | have hs : {i : Fin 3 | z i = 0} = {2} := by
        ext i; fin_cases i <;> simp_all; done
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs,
        Set.image_singleton, Set.ncard_singleton] at hz
      omega
    | have hs : {i : Fin 3 | z i = 0} = ∅ := by
        ext i; fin_cases i <;> simp_all
      rw [componentSupport_inclusion_eq_zeroCoordinates, hs, Set.image_empty, Set.ncard_empty] at hz
      omega

public def constructedCentralUpperAxisChart : Fin 3 → ChartIndex :=
  ![(true, 0), (true, -e₁), (true, -e₂)]

public def constructedCentralUpperAxisIndex : Fin 3 → Fin 3 := ![2, 1, 0]

public theorem upperSingleAxis_mem_edge_or_phaseFace (j : Fin 3) (z : ℂ) :
    inclusion (constructedCentralUpperAxisChart j)
        (singleAxis (constructedCentralUpperAxisIndex j) z) ∈
      (constructedCentralEdgeCarrier j '' Metric.closedBall 0 1) ∪
        (constructedCentralPhaseFaceCarrier j '' Metric.ball 0 1) := by
  have h := upperAxisTwo_mem_edge_or_phaseFace z
  fin_cases j
  · have heq : singleAxis 2 z = upperAxisTwo z := by
      funext i
      fin_cases i <;> simp [singleAxis, upperAxisTwo]
    simpa [constructedCentralEdgeCarrier, constructedCentralPhaseFaceCarrier,
      constructedCentralUpperAxisChart, constructedCentralUpperAxisIndex, heq] using h
  · rcases h with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
    · refine Or.inl ⟨x, hx, ?_⟩
      have hr := congrArg a2CyclicCarrier heq
      rw [a2CyclicCarrier_constructedCentralEdgeZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicChartIndex_upper_zero] at hr
      simpa [constructedCentralEdgeCarrier, constructedCentralUpperAxisChart,
        constructedCentralUpperAxisIndex, a2CyclicRaw, a2CyclicRawUpper_upperAxisTwo] using hr
    · refine Or.inr ⟨x, hx, ?_⟩
      have hr := congrArg a2CyclicCarrier heq
      rw [a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicChartIndex_upper_zero] at hr
      simpa [constructedCentralPhaseFaceCarrier, constructedCentralUpperAxisChart,
        constructedCentralUpperAxisIndex, a2CyclicRaw, a2CyclicRawUpper_upperAxisTwo] using hr
  · rcases h with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
    · refine Or.inl ⟨x, hx, ?_⟩
      have hr := congrArg (a2CyclicCarrier ∘ a2CyclicCarrier) heq
      simp only [Function.comp_apply] at hr
      rw [a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
        a2CyclicChartIndex_sq_upper_zero] at hr
      simpa [constructedCentralEdgeCarrier, constructedCentralUpperAxisChart,
        constructedCentralUpperAxisIndex, a2CyclicRaw, a2CyclicRawUpper_sq_upperAxisTwo] using hr
    · refine Or.inr ⟨x, hx, ?_⟩
      have hr := congrArg (a2CyclicCarrier ∘ a2CyclicCarrier) heq
      simp only [Function.comp_apply] at hr
      rw [a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier,
        a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
        a2CyclicChartIndex_sq_upper_zero] at hr
      simpa [constructedCentralPhaseFaceCarrier, constructedCentralUpperAxisChart,
        constructedCentralUpperAxisIndex, a2CyclicRaw, a2CyclicRawUpper_sq_upperAxisTwo] using hr

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem exists_actualCentral_deck_translate_singleAxis
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (a : ChartIndex) (j : Fin 3) (z : ℂ)
    (hp : (p.1.1 : Carrier) = inclusion a (singleAxis j z)) (v : ToricLattice) :
    ∃ (q : actualLocalCuspCentralSubMulAction W) (w : ℂ),
      Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
        (actualLocalCuspCentralSubMulAction W)) q = Quotient.mk _ p ∧
        (q.1.1 : Carrier) = inclusion (a.1, v) (singleAxis j w) := by
  let _ := actualLocalCuspQuotientAction W
  obtain ⟨lambda, hlambda⟩ := shearVector_surjective (v - a.2)
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let g := Multiplicative.ofAdd lambda
  let q : actualLocalCuspCentralSubMulAction W := g • p
  let c := CuspToricPhaseAction.phaseEmbedding (C.phase lambda (constructedModel.t p.1))
  refine ⟨q, torusChartCoordinates (a.1, v) c j * z, ?_, ?_⟩
  · apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) q p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  · have hchart : translateChartIndex lambda a = (a.1, v) := by
      simp [translateChartIndex, hlambda]
    change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda p.1).1 : Carrier) = _
    rw [← C.psiMap_eq_generic, C.psiMap_coe]
    change carrierTorusActionFun c (carrierFanShearFun lambda (p.1.1 : Carrier)) = _
    rw [hp, carrierFanShearFun_inclusion, hchart, carrierTorusActionFun_inclusion]
    congr 1
    funext i
    by_cases hi : i = j <;> simp [singleAxis, hi]

public def constructedCentralPhaseFaceOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Fin 3 → (Fin 2 → ℝ) → ActualLocalCuspCentralOrbitQuotient W :=
  ![constructedCentralPhaseFaceZeroOrbit W, constructedCentralPhaseFaceOneOrbit W,
    constructedCentralPhaseFaceTwoOrbit W]

public def constructedCentralBoundaryTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedCentralOneSkeleton W ∪
    ⋃ j : Fin 3, constructedCentralPhaseFaceOrbit W j '' Metric.ball 0 1

public theorem constructedCentralCarrier_mem_edge_or_phaseFace_implies_mem_boundaryTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W) (j : Fin 3)
    (hp : (p.1.1 : Carrier) ∈
      (constructedCentralEdgeCarrier j '' Metric.closedBall 0 1) ∪
        (constructedCentralPhaseFaceCarrier j '' Metric.ball 0 1)) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p ∈
        constructedCentralBoundaryTwoSkeleton W := by
  let _ := actualLocalCuspQuotientAction W
  rcases hp with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
  · apply Or.inl
    apply Established.constructedCentralCarrier_eq_oneCell_implies_mem_oneSkeleton W p j x hx
    fin_cases j <;> exact heq.symm
  · apply Or.inr
    refine Set.mem_iUnion.mpr ⟨j, x, hx, ?_⟩
    fin_cases j
    all_goals
      apply congrArg (Quotient.mk (MulAction.orbitRel
        (Multiplicative ParameterLattice) (actualLocalCuspCentralSubMulAction W)))
      apply Subtype.ext
      apply Subtype.ext
      exact heq

public theorem exists_standardBoundaryChart (upper : Bool) (j : Fin 3) :
    ∃ (k : Fin 3) (v : ToricLattice), ∀ z : ℂ,
      inclusion (upper, v) (singleAxis j z) ∈
        (constructedCentralEdgeCarrier k '' Metric.closedBall 0 1) ∪
          (constructedCentralPhaseFaceCarrier k '' Metric.ball 0 1) := by
  cases upper
  · exact ⟨j, 0, lowerSingleAxis_mem_edge_or_phaseFace j⟩
  · fin_cases j
    · exact ⟨2, -e₂, upperSingleAxis_mem_edge_or_phaseFace 2⟩
    · exact ⟨1, -e₁, upperSingleAxis_mem_edge_or_phaseFace 1⟩
    · exact ⟨0, 0, upperSingleAxis_mem_edge_or_phaseFace 0⟩

public theorem constructedCentral_support_ge_two_mem_boundaryTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (hp : 2 ≤ (componentSupport constructedModel (p.1.1 : Carrier)).ncard) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p ∈
        constructedCentralBoundaryTwoSkeleton W := by
  obtain ⟨a, z, ha⟩ := inclusion_jointly_surjective (p.1.1 : Carrier)
  have hz : 2 ≤ (componentSupport constructedModel (inclusion a z)).ncard := by
    simpa only [ha] using hp
  obtain ⟨j, hj⟩ := exists_singleAxis_of_componentSupport_ncard_ge_two a z hz
  obtain ⟨k, v, hv⟩ := exists_standardBoundaryChart a.1 j
  have hrepr : (p.1.1 : Carrier) = inclusion a (singleAxis j (z j)) := by
    rw [← ha]
    exact congrArg (inclusion a) hj
  obtain ⟨q, w, hq, hw⟩ :=
    exists_actualCentral_deck_translate_singleAxis W p a j (z j) hrepr v
  rw [← hq]
  apply constructedCentralCarrier_mem_edge_or_phaseFace_implies_mem_boundaryTwoSkeleton W q k
  rw [hw]
  exact hv w

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
