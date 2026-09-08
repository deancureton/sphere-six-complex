module

public import SphereSixComplex.Topology.CuspPhaseCentralCompatibility
public import SphereSixComplex.Topology.StandardA2ToricBoundaryFaceCoverage
public import SphereSixComplex.Topology.StandardA2PhaseCellDisjointness

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricModel.Construction
open StandardInfiniteA2ToricModel.Established

public def fourthPhaseEdgeZeroSweep (c : Circle) (x : Fin 1 → ℝ) : Carrier :=
  constructedModel.torusAction
    (CuspToricPhaseAction.phaseEmbedding ![1, Circle.toUnits c])
    (constructedCentralEdgeZeroCarrier x)

public theorem fourthPhaseEdgeZeroSweep_lower (c : Circle) (x : Fin 1 → ℝ)
    (hx : x 0 ≤ 0) :
    fourthPhaseEdgeZeroSweep c x =
      inclusion (false, 0) (lowerAxisZero ((c : ℂ)⁻¹ * (1 + x 0))) := by
  unfold fourthPhaseEdgeZeroSweep constructedCentralEdgeZeroCarrier
  rw [ite_eq_left hx]
  have he (w : ℂ) : lowerAxisZero w = singleAxis 0 w := by
    ext i; fin_cases i <;> rfl
  rw [constructedCentralEdgeZeroLowerBranch, he]
  rw [lowerAxis_phase_action]
  simp [← he]

public theorem fourthPhaseEdgeZeroSweep_upper (c : Circle) (x : Fin 1 → ℝ)
    (hx : ¬x 0 ≤ 0) :
    fourthPhaseEdgeZeroSweep c x =
      inclusion (true, 0) (upperAxisTwo ((c : ℂ) * (1 - x 0))) := by
  unfold fourthPhaseEdgeZeroSweep constructedCentralEdgeZeroCarrier
  rw [ite_eq_right hx]
  have he (w : ℂ) : upperAxisTwo w = singleAxis 2 w := by
    ext i; fin_cases i <;> rfl
  rw [constructedCentralEdgeZeroUpperBranch, he]
  rw [upperAxis_phase_action]
  simp [← he]

public theorem circle_mul_pos_not_nonnegReal (c : Circle) (hc : c ≠ 1)
    (r : ℝ) (hr : 0 < r) :
    ¬(((c : ℂ) * r).im = 0 ∧ 0 ≤ ((c : ℂ) * r).re) := by
  rintro ⟨him, hre⟩
  have hci : (c : ℂ).im = 0 := by
    simpa [Complex.mul_im, hr.ne'] using him
  have hcr : 0 ≤ (c : ℂ).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hre
    exact nonneg_of_mul_nonneg_left hre hr
  apply hc
  apply Subtype.ext
  apply Complex.ext
  · have hn := c.norm_coe
    have hsq : (c : ℂ).re ^ 2 = 1 := by
      have h := congrArg (fun t : ℝ ↦ t ^ 2) hn
      simp only [Complex.sq_norm, Complex.normSq_apply, hci, mul_zero, add_zero,
        one_pow] at h
      nlinarith
    change (c : ℂ).re = 1
    nlinarith
  · simpa using hci

public theorem circle_mul_pos_injective (c d : Circle) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (h : (c : ℂ) * r = (d : ℂ) * s) :
    c = d ∧ r = s := by
  have hrs : r = s := by
    have hn := congrArg norm h
    simpa [norm_mul, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      abs_of_pos hs] using hn
  refine ⟨?_, hrs⟩
  apply Subtype.ext
  rw [← hrs] at h
  exact mul_right_cancel₀ (by exact_mod_cast hr.ne') h

public theorem fourthPhaseEdgeZeroSweep_lower_mem_phase (c : Circle) (hc : c ≠ 1)
    (x : Fin 1 → ℝ) (hx : -1 < x 0) (hx' : x 0 ≤ 0) :
    fourthPhaseEdgeZeroSweep c x ∈
      constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
  rw [fourthPhaseEdgeZeroSweep_lower c x hx']
  apply lowerAxisZero_mem_phaseFace_of_not_nonnegReal
  simpa using circle_mul_pos_not_nonnegReal c⁻¹ (inv_ne_one.mpr hc)
    (1 + x 0) (by linarith)

public theorem fourthPhaseEdgeZeroSweep_mem_phase (c : Circle) (hc : c ≠ 1)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    fourthPhaseEdgeZeroSweep c x ∈
      constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
  have hxabs : |x 0| < 1 := by
    simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs] using hx
  rcases abs_lt.mp hxabs with ⟨hxlo, hxhi⟩
  by_cases hx' : x 0 ≤ 0
  · exact fourthPhaseEdgeZeroSweep_lower_mem_phase c hc x hxlo hx'
  rw [fourthPhaseEdgeZeroSweep_upper c x hx']
  have hr : 0 < 1 - x 0 := by linarith
  have hz : (c : ℂ) * (1 - x 0) ≠ 0 :=
    mul_ne_zero c.coe_ne_zero (by exact_mod_cast hr.ne')
  have he := inclusion_lowerAxisZero_eq_upperAxisTwo 0 _ (inv_ne_zero hz)
  simp only [inv_inv] at he
  rw [← he]
  apply lowerAxisZero_mem_phaseFace_of_not_nonnegReal
  rw [mul_inv]
  simpa using circle_mul_pos_not_nonnegReal c⁻¹ (inv_ne_one.mpr hc) (1 - x 0)⁻¹
    (inv_pos.mpr hr)

public def phaseEdgeRadius (r : ℝ) : ℝ := if r ≤ 0 then 1 + r else (1 - r)⁻¹

public theorem phaseEdgeRadius_pos {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    0 < phaseEdgeRadius r := by
  unfold phaseEdgeRadius
  split_ifs
  · linarith [hr.1]
  · exact inv_pos.mpr (by linarith [hr.2])

public theorem phaseEdgeRadius_le_one {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    phaseEdgeRadius r ≤ 1 ↔ r ≤ 0 := by
  unfold phaseEdgeRadius
  split_ifs with h
  · simp only [h, iff_true]
    linarith
  · rw [inv_le_one₀ (by linarith [hr.2] : 0 < 1 - r)]
    constructor <;> intro h' <;> linarith

public theorem phaseEdgeRadius_recover {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    (if phaseEdgeRadius r ≤ 1 then phaseEdgeRadius r - 1
      else 1 - (phaseEdgeRadius r)⁻¹) = r := by
  simp only [phaseEdgeRadius_le_one hr]
  by_cases h : r ≤ 0 <;> simp [phaseEdgeRadius, h]

public theorem phaseEdgeRadius_injOn : Set.InjOn phaseEdgeRadius (Ioo (-1 : ℝ) 1) := by
  intro r hr s hs hrs
  rw [← phaseEdgeRadius_recover hr, ← phaseEdgeRadius_recover hs, hrs]

public theorem phaseEdgeRadius_surjective {s : ℝ} (hs : 0 < s) :
    ∃ r ∈ Ioo (-1 : ℝ) 1, phaseEdgeRadius r = s := by
  by_cases h : s ≤ 1
  · refine ⟨s - 1, ⟨by linarith, by linarith⟩, ?_⟩
    simp [phaseEdgeRadius, show s - 1 ≤ 0 by linarith]
  · have hsi : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_of_not_ge h)
    have hsp : 0 < s⁻¹ := inv_pos.mpr hs
    refine ⟨1 - s⁻¹, ⟨by linarith, by linarith⟩, ?_⟩
    simp [phaseEdgeRadius, show ¬1 - s⁻¹ ≤ 0 by linarith]

public theorem fourthPhaseEdgeZeroSweep_radius (c : Circle) (x : Fin 1 → ℝ)
    (hx : x ∈ Metric.ball 0 1) :
    fourthPhaseEdgeZeroSweep c x =
      inclusion (false, 0) (lowerAxisZero ((c : ℂ)⁻¹ * phaseEdgeRadius (x 0))) := by
  have hxb : x 0 ∈ Ioo (-1 : ℝ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt] using hx
  obtain ⟨hxlo, hxhi⟩ := hxb
  by_cases hx' : x 0 ≤ 0
  · rw [fourthPhaseEdgeZeroSweep_lower c x hx']
    simp [phaseEdgeRadius, hx']
  rw [fourthPhaseEdgeZeroSweep_upper c x hx']
  have hr : 0 < 1 - x 0 := by linarith
  have hz : (c : ℂ) * (1 - x 0) ≠ 0 :=
    mul_ne_zero c.coe_ne_zero (by exact_mod_cast hr.ne')
  have heq := inclusion_lowerAxisZero_eq_upperAxisTwo 0
    ((c : ℂ) * (1 - x 0))⁻¹ (inv_ne_zero hz)
  simpa [phaseEdgeRadius, hx', mul_inv, mul_comm] using heq.symm

public theorem fourthPhaseEdgeZeroSweep_injective (c d : Circle)
    (x y : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) (hy : y ∈ Metric.ball 0 1)
    (h : fourthPhaseEdgeZeroSweep c x = fourthPhaseEdgeZeroSweep d y) :
    c = d ∧ x = y := by
  rw [fourthPhaseEdgeZeroSweep_radius c x hx,
    fourthPhaseEdgeZeroSweep_radius d y hy] at h
  have hraw := (inclusion_isOpenEmbedding (false, 0)).injective h
  have hz := congrFun hraw 0
  simp only [lowerAxisZero, Matrix.cons_val_zero] at hz
  have hx' : x 0 ∈ Ioo (-1 : ℝ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt] using hx
  have hy' : y 0 ∈ Ioo (-1 : ℝ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt] using hy
  obtain ⟨hcd, hxy⟩ := circle_mul_pos_injective c⁻¹ d⁻¹
    (phaseEdgeRadius (x 0)) (phaseEdgeRadius (y 0))
    (phaseEdgeRadius_pos hx') (phaseEdgeRadius_pos hy') hz
  refine ⟨inv_injective hcd, ?_⟩
  funext j
  fin_cases j
  exact phaseEdgeRadius_injOn hx' hy' hxy

public theorem lowerAxisZero_mem_fourthPhaseEdgeZeroSweep (z : ℂ)
    (hz : ¬(z.im = 0 ∧ 0 ≤ z.re)) :
    ∃ c : Circle, c ≠ 1 ∧ ∃ x ∈ Metric.ball (0 : Fin 1 → ℝ) 1,
      fourthPhaseEdgeZeroSweep c x = inclusion (false, 0) (lowerAxisZero z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  let d : Circle := ⟨z / (‖z‖ : ℂ), by
    simp [Submonoid.unitSphere, hzn.ne']⟩
  have hd : (d : ℂ) * (‖z‖ : ℂ) = z :=
    div_mul_cancel₀ _ (by exact_mod_cast hzn.ne')
  have hd1 : d ≠ 1 := by
    intro h
    have he : (‖z‖ : ℂ) = z := by simpa [h] using hd
    apply hz
    rw [← he]
    simp [norm_nonneg]
  obtain ⟨r, hr, hrs⟩ := phaseEdgeRadius_surjective hzn
  let x : Fin 1 → ℝ := fun _ ↦ r
  have hx : x ∈ Metric.ball 0 1 := by
    simpa [x, Metric.mem_ball, dist_zero_right, Pi.norm_def, Real.norm_eq_abs, abs_lt]
      using hr
  refine ⟨d⁻¹, inv_ne_one.mpr hd1, x, hx, ?_⟩
  rw [fourthPhaseEdgeZeroSweep_radius _ x hx]
  simpa [x, hrs] using congrArg (fun w ↦ inclusion (false, 0) (lowerAxisZero w)) hd

public theorem phaseFaceZero_lowerSlit (p : Carrier)
    (hp : p ∈ constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1) :
    ∃ z : ℂ, ¬(z.im = 0 ∧ 0 ≤ z.re) ∧
      p = inclusion (false, 0) (lowerAxisZero z) := by
  obtain ⟨x, hx, rfl⟩ := hp
  have hcut (z : ℂ)
      (he : constructedCentralPhaseFaceZeroCarrier x =
        inclusion (false, 0) (lowerAxisZero z)) :
      ¬(z.im = 0 ∧ 0 ≤ z.re) := by
    rintro ⟨hz, hz'⟩
    have hreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz]
    obtain ⟨y, hy, he'⟩ := lowerAxisZero_mem_edgeZero_of_nonnegReal z.re hz'
    exact constructedCentralPhaseFaceZeroCarrier_ne_edgeZero hx hy
      (he.trans (by simpa [hreal] using he'.symm))
  by_cases h : x 0 ≤ 0
  · have he : constructedCentralPhaseFaceZeroCarrier x =
        inclusion (false, 0) (lowerAxisZero (centralPhaseDiskLowerCoordinate x)) := by
      simp [constructedCentralPhaseFaceZeroCarrier, h]
    exact ⟨_, hcut _ he, he⟩
  · have he : constructedCentralPhaseFaceZeroCarrier x =
        inclusion (true, 0) (upperAxisTwo (centralPhaseDiskUpperCoordinate x)) := by
      simp [constructedCentralPhaseFaceZeroCarrier, h]
    have hz : centralPhaseDiskUpperCoordinate x ≠ 0 := by
      intro hz
      apply constructedCentralPhaseFaceZeroCarrier_ne_edgeZero hx
        (show (fun _ : Fin 1 ↦ (1 : ℝ)) ∈ Metric.closedBall 0 1 by
          simp [Metric.mem_closedBall, dist_zero_right, Pi.norm_def])
      simpa [hz, constructedCentralEdgeZeroCarrier, show ¬(1 : ℝ) ≤ 0 by norm_num,
        constructedCentralEdgeZeroUpperBranch] using he
    have he' : constructedCentralPhaseFaceZeroCarrier x =
        inclusion (false, 0) (lowerAxisZero (centralPhaseDiskUpperCoordinate x)⁻¹) := by
      rw [he, inclusion_lowerAxisZero_eq_upperAxisTwo 0 _ (inv_ne_zero hz), inv_inv]
    exact ⟨_, hcut _ he', he'⟩

public theorem fourthPhaseEdgeZeroSweep_image :
    (fun p : Circle × (Fin 1 → ℝ) ↦ fourthPhaseEdgeZeroSweep p.1 p.2) ''
      ({c | c ≠ 1} ×ˢ Metric.ball 0 1) =
      constructedCentralPhaseFaceZeroCarrier '' Metric.ball 0 1 := by
  ext p
  constructor
  · rintro ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩
    exact fourthPhaseEdgeZeroSweep_mem_phase c hc x hx
  · intro hp
    obtain ⟨z, hz, rfl⟩ := phaseFaceZero_lowerSlit p hp
    obtain ⟨c, hc, x, hx, he⟩ := lowerAxisZero_mem_fourthPhaseEdgeZeroSweep z hz
    exact ⟨(c, x), ⟨hc, hx⟩, he⟩

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
