/-
The normalized splitting argument follows plby/HopfProblem, Solution.lean,
lines 163705–163713 and 165288–165403, commit 9ac8a456b526527837d7082ff775213ca8bc9809 (Apache-2.0):
https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean
This version directly constructs functions from the cocycle, without auxiliary structures.
-/
module

public import SphereSixComplex.Analysis.CocycleForcing
public import SphereSixComplex.Analysis.CauchyGreenInfinity
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

noncomputable section

open Set Function
open scoped ContDiff

namespace SphereSixComplex.Analysis.CauchyGreen

theorem exists_normalized_holomorphic_cocycle_solution {ι : Type*} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z)
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ (s : ι → ℂ → ℂ) (sInfinity : ℂ → ℂ),
      (∀ i, AnalyticOnNhd ℂ (s i) (U i)) ∧
      AnalyticOnNhd ℂ sInfinity (Metric.ball 0 R⁻¹) ∧ sInfinity 0 = 0 ∧
      (∀ i j z, z ∈ U i → z ∈ U j → s i z - s j z = h i j z) ∧
      ∀ z, R < ‖z‖ → s i₀ z = sInfinity z⁻¹ := by
  obtain ⟨t, f, V, ht, htrans, hf, hfc, hfEq, _, hRV, _, ht0, hsupport⟩ :=
    exists_normalized_cocycle_forcing hU hcover hh hc i₀ R hRU
  obtain ⟨hcg, hsolve⟩ := cauchyGreen_smooth_dbar_solution hf hfc
  have hbound : ∀ z ∈ Function.support f, ‖z‖ ≤ R := by
    intro z hz
    have hzR := hsupport (subset_tsupport f hz)
    exact (show ‖z‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hzR).le
  refine ⟨fun i z ↦ t i z - cauchyGreen f z, fun u ↦ -cauchyGreenInfinity f u,
    ?_, (analyticOnNhd_cauchyGreenInfinity hf.continuous hfc hR hbound).neg, ?_, ?_, ?_⟩
  · intro i
    apply analyticOnNhd_of_dbar_eq_zero (hU i)
    · exact ((ht i).differentiableOn (by simp)).sub
        (hcg.differentiable (by simp)).differentiableOn
    · intro z hz
      rw [dbar_sub (((ht i z hz).contDiffAt ((hU i).mem_nhds hz)).differentiableAt
        (by simp)) (hcg.differentiable (by simp) z), hsolve, hfEq i z hz, sub_self]
  · simp only [cauchyGreenInfinity_zero, neg_zero]
  · intro i j z hi hj
    simpa only [sub_sub_sub_cancel_right] using htrans i j z hi hj
  · intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hz)
    have hzV : z ∈ V := hRV (by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz.le)
    change t i₀ z - cauchyGreen f z = -cauchyGreenInfinity f z⁻¹
    rw [ht0 hzV, zero_sub, cauchyGreenInfinity_inv f hz0]

theorem exists_negativeOne_holomorphic_cocycle_solution {ι : Type*} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z)
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ (s : ι → ℂ → ℂ) (sInfinity : ℂ → ℂ),
      (∀ i, AnalyticOnNhd ℂ (s i) (U i)) ∧
      AnalyticOnNhd ℂ sInfinity (Metric.ball 0 R⁻¹) ∧
      (∀ i j z, z ∈ U i → z ∈ U j → s i z - s j z = h i j z) ∧
      ∀ z, R < ‖z‖ → s i₀ z = z⁻¹ * sInfinity z⁻¹ := by
  obtain ⟨s, g, hs, hg, hg0, hdiff, hinf⟩ :=
    exists_normalized_holomorphic_cocycle_solution hU hcover hh hc i₀ hR hRU
  refine ⟨s, dslope g 0, hs, ?_, hdiff, ?_⟩
  · apply (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr
    exact (Complex.differentiableOn_dslope
      (Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hR))).mpr hg.differentiableOn
  · intro z hz
    rw [hinf z hz]
    exact (show z⁻¹ * dslope g 0 z⁻¹ = g z⁻¹ by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero hg0 z⁻¹).symm

end SphereSixComplex.Analysis.CauchyGreen
