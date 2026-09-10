/-
SPDX-License-Identifier: Apache-2.0
Adapted from plby/HopfProblem, Solution.lean, commit
9ac8a456b526527837d7082ff775213ca8bc9809, lines 165164-165286:
https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean
The source is released under Apache-2.0. This focused adaptation changes imports,
namespace, helper names and formatting.
-/
module

public import SphereSixComplex.Prerequisites.Analysis.CauchyGreen
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter
open scoped Convolution ContDiff Topology

namespace SphereSixComplex.Analysis.CauchyGreen

def cauchyGreenInfinity (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, u * (1 - w * u)⁻¹ * f w

@[simp]
theorem cauchyGreenInfinity_zero (f : ℂ → ℂ) : cauchyGreenInfinity f 0 = 0 := by
  simp [cauchyGreenInfinity]

private theorem area_denominator_ne_zero {R : ℝ} (hR : 0 < R)
    {u w : ℂ} (hu : u ∈ Metric.ball 0 R⁻¹) (hw : ‖w‖ ≤ R) : 1 - w * u ≠ 0 := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  have hmul : ‖w * u‖ < 1 := by
    rw [norm_mul]
    calc
      ‖w‖ * ‖u‖ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg u)
      _ < R * R⁻¹ := (mul_lt_mul_of_pos_left hu' hR)
      _ = 1 := mul_inv_cancel₀ hR.ne'
  intro heq
  have hwu : w * u = 1 := (sub_eq_zero.mp heq).symm
  simp [hwu] at hmul

private theorem area_denominator_lower_bound {R r : ℝ} (hR : 0 < R)
    {x w : ℂ} (hx : x ∈ Metric.ball 0 r) (hw : ‖w‖ ≤ R) : 1 - R * r ≤ ‖1 - w * x‖ := by
  have hx' : ‖x‖ ≤ r := le_of_lt (by simpa using hx)
  have hmul : ‖w * x‖ ≤ R * r := by
    rw [norm_mul]
    exact mul_le_mul hw hx' (norm_nonneg x) hR.le
  calc
    1 - R * r ≤ 1 - ‖w * x‖ := sub_le_sub_left hmul 1
    _ = ‖(1 : ℂ)‖ - ‖w * x‖ := by rw [NormOneClass.norm_one]
    _ ≤ ‖1 - w * x‖ := norm_sub_norm_le _ _

private theorem area_reciprocal_kernel_hasDerivAt {w x : ℂ}
    (hne : 1 - w * x ≠ 0) : HasDerivAt (fun y : ℂ ↦ y * (1 - w * y)⁻¹) (1 / (1 - w * x) ^ 2) x :=
  by
  have hn : HasDerivAt (fun y : ℂ ↦ y) 1 x := hasDerivAt_id x
  have hd : HasDerivAt (fun y : ℂ ↦ 1 - w * y) (-w) x := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id x).const_mul w).const_sub 1
  have hnum : (1 : ℂ) * (1 - w * x) - x * -w = 1 := by ring
  simpa only [Pi.div_apply, hnum, div_eq_mul_inv] using! hn.div hd hne

theorem hasDerivAt_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : MeasureTheory.Integrable f) (hR : 0 < R) (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R)
    {u : ℂ} (hu : u ∈ Metric.ball 0 R⁻¹) :
    HasDerivAt (cauchyGreenInfinity f)
      ((1 / (Real.pi : ℂ)) * ∫ w : ℂ, (1 / (1 - w * u) ^ 2) * f w) u := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  obtain ⟨r, hur, hrR⟩ := exists_between hu'
  have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 R⁻¹ := Metric.ball_subset_ball hrR.le
  have humem : u ∈ Metric.ball (0 : ℂ) r := by simpa using hur
  have hd : 0 < 1 - R * r := by
    have hlt : R * r < 1 := by
      calc
        R * r < R * R⁻¹ := mul_lt_mul_of_pos_left hrR hR
        _ = 1 := mul_inv_cancel₀ hR.ne'
    linarith
  have hmeas (x : ℂ) :
    MeasureTheory.AEStronglyMeasurable (fun w : ℂ ↦ x * (1 - w * x)⁻¹ * f w)
      MeasureTheory.MeasureSpace.volume := by
    apply MeasureTheory.AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hint : MeasureTheory.Integrable (fun w : ℂ ↦ u * (1 - w * u)⁻¹ * f w) := by
    refine (hf.norm.const_mul (‖u‖ * (1 - R * r)⁻¹)).mono' (hmeas u) ?_
    filter_upwards with w
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv]
      gcongr
      exact area_denominator_lower_bound hR humem hwb
  change HasDerivAt (fun x ↦ cauchyGreenInfinity f x) _ u
  simp only [cauchyGreenInfinity]
  apply HasDerivAt.const_mul
  refine
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun x w : ℂ ↦
        (1 / (1 - w * x) ^ 2) * f w) (bound := fun w : ℂ ↦ ((1 - R * r) ^ 2)⁻¹ * ‖f w‖)
        (Metric.isOpen_ball.mem_nhds humem) (Filter.Eventually.of_forall hmeas) hint ?_ ?_ ?_
        ?_).2
  · apply MeasureTheory.AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv, norm_pow, one_div]
      gcongr
      exact area_denominator_lower_bound hR hx hwb
  · exact hf.norm.const_mul _
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simpa only [hw, MulZeroClass.mul_zero] using hasDerivAt_const x (0 : ℂ)
    · exact
        (area_reciprocal_kernel_hasDerivAt
              (area_denominator_ne_zero hR (hsub hx) (hbound w hw))).mul_const
          (f w)

theorem analyticOnNhd_cauchyGreenInfinity_of_integrable {f : ℂ → ℂ} {R : ℝ}
    (hf : MeasureTheory.Integrable f) (hR : 0 < R) (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (Metric.ball 0 R⁻¹) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro u hu
  exact (hasDerivAt_cauchyGreenInfinity hf hR hbound hu).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < R)
    (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (Metric.ball 0 R⁻¹) :=
  analyticOnNhd_cauchyGreenInfinity_of_integrable (hf.integrable_of_hasCompactSupport hfc) hR
    hbound

theorem cauchyGreenInfinity_inv (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    cauchyGreenInfinity f z⁻¹ = cauchyGreen f z := by
  unfold cauchyGreenInfinity cauchyGreen
  congr 1
  calc
    (∫ w : ℂ, z⁻¹ * (1 - w * z⁻¹)⁻¹ * f w) = ∫ w : ℂ, (z - w)⁻¹ * f w := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      have hden : 1 - w * z⁻¹ = (z - w) * z⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hz]
      rw [hden, mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    _ = ∫ w : ℂ, w⁻¹ * f (z - w) := by
      simpa only [sub_sub_self] using
        MeasureTheory.integral_sub_left_eq_self (fun w : ℂ ↦ w⁻¹ * f (z - w))
          MeasureTheory.MeasureSpace.volume z

theorem analyticAt_cauchyGreenInfinity_zero {f : ℂ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    AnalyticAt ℂ (cauchyGreenInfinity f) 0 := by
  obtain ⟨R, hR, hbound⟩ := hfc.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hs : ∀ w ∈ Function.support f, ‖w‖ ≤ R := by
    intro w hw
    exact (show ‖w‖ < R by simpa using hbound (subset_tsupport f hw)).le
  exact analyticOnNhd_cauchyGreenInfinity hf hfc hR hs 0
    (by simpa using inv_pos.mpr hR)

theorem tendsto_cauchyGreen_cobounded {f : ℂ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (cauchyGreen f) (Bornology.cobounded ℂ) (𝓝 0) := by
  have h := (analyticAt_cauchyGreenInfinity_zero hf hfc).continuousAt.tendsto.comp
    (tendsto_inv₀_cobounded (α := ℂ))
  simp only [cauchyGreenInfinity_zero] at h
  apply h.congr'
  filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
  exact cauchyGreenInfinity_inv f hz

end SphereSixComplex.Analysis.CauchyGreen
