/-
The Cauchy–Riemann helpers adapt plby/HopfProblem, Solution.lean, lines 164644–164700,
commit 9ac8a456b526527837d7082ff775213ca8bc9809 (Apache-2.0):
https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean
The cocycle forcing construction adapts the argument of lines 164701–164828,
without introducing a local-potential structure.
-/
module

public import SphereSixComplex.Analysis.CauchyGreen
public import SphereSixComplex.Analysis.NormalizedCocycle
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace SphereSixComplex.Analysis.CauchyGreen

theorem dbar_eq_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = 0 ↔ fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
  constructor
  · intro h
    have hs : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      simpa only [dbar, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using h
    have hm := congrArg (fun w : ℂ ↦ -Complex.I * w) hs
    simp only [mul_add, neg_mul, ← mul_assoc, Complex.I_mul_I, neg_neg,
      MulZeroClass.mul_zero] at hm
    linear_combination hm
  · intro h
    rw [dbar, h, ← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, zero_div]

theorem differentiableAt_complex_iff_dbar {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ dbar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, dbar_eq_zero_iff]
  rfl

theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 :=
  (differentiableAt_complex_iff_dbar.mp hf).2

theorem analyticOnNhd_of_dbar_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (hd : ∀ z ∈ U, dbar f z = 0) : AnalyticOnNhd ℂ f U := by
  apply (Complex.analyticOnNhd_iff_differentiableOn hU).mpr
  intro z hz
  exact
    ((differentiableAt_complex_iff_dbar).mpr
        ⟨(hf z hz).differentiableAt (hU.mem_nhds hz), hd z hz⟩).differentiableWithinAt

theorem dbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w ↦ f w - g w) z = dbar f z - dbar g z := by
  simp only [dbar_eq_dbarLinear, fderiv_fun_sub hf hg, map_sub]

theorem contDiffAt_dbar {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbar f) z := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact dbarLinear.contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))

theorem dbar_eq_of_sub_differentiableAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hfg : DifferentiableAt ℂ (fun w ↦ f w - g w) z) : dbar f z = dbar g z := by
  have he := dbar_eq_zero_of_differentiableAt hfg
  rw [dbar_sub hf hg] at he
  exact sub_eq_zero.mp he

theorem exists_normalized_cocycle_forcing {ι : Type*} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z)
    (i₀ : ι) (R : ℝ) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ (s : ι → ℂ → ℂ) (f : ℂ → ℂ) (V : Set ℂ),
      (∀ i, ContDiffOn ℝ ∞ (s i) (U i)) ∧
      (∀ i j z, z ∈ U i → z ∈ U j → s i z - s j z = h i j z) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ i z, z ∈ U i → f z = dbar (s i) z) ∧
      IsOpen V ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ V ∧ V ⊆ U i₀ ∧
      Set.EqOn (s i₀) (fun _ ↦ 0) V ∧ tsupport f ⊆ Metric.ball (0 : ℂ) R := by
  classical
  have hsmooth i j : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (h i j) (U i ∩ U j) :=
    ((hh i j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ |>.contMDiffOn
  obtain ⟨V, s, hVo, hRV, hVU, hs, htrans, hs0, _⟩ :=
    HolomorphicCousin.exists_normalized_smooth_cocycle_cochain hU hcover hsmooth hc i₀
      Metric.isOpen_ball.isClosed_compl hRU
  have hsAt {i : ι} {z : ℂ} (hz : z ∈ U i) : ContDiffAt ℝ ∞ (s i) z :=
    ((hs i).contDiffOn z hz).contDiffAt ((hU i).mem_nhds hz)
  let f : ℂ → ℂ := fun z ↦ dbar (s (hcover z).choose) z
  have hfEq (i : ι) (z : ℂ) (hz : z ∈ U i) : f z = dbar (s i) z := by
    have ha : AnalyticOnNhd ℂ (fun w ↦ s (hcover z).choose w - s i w)
        (U (hcover z).choose ∩ U i) :=
      (hh (hcover z).choose i).congr ((hU _).inter (hU _))
        (fun w hw ↦ (htrans _ _ w hw.1 hw.2).symm)
    exact dbar_eq_of_sub_differentiableAt
      ((hsAt (hcover z).choose_spec).differentiableAt (by simp))
      ((hsAt hz).differentiableAt (by simp))
      (ha z ⟨(hcover z).choose_spec, hz⟩).differentiableAt
  have hfSmooth : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    obtain ⟨i, hi⟩ := hcover z
    apply (contDiffAt_dbar (hsAt hi)).congr_of_eventuallyEq
    filter_upwards [(hU i).mem_nhds hi] with w hw
    exact hfEq i w hw
  have hfZero : Set.EqOn f (fun _ ↦ 0) V := by
    intro z hz
    rw [hfEq i₀ z (hVU hz)]
    apply dbar_eq_zero_of_differentiableAt
    apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hVo.mem_nhds hz] with w hw
    exact hs0 hw
  have hfSupportV : tsupport f ⊆ Vᶜ := by
    apply closure_minimal ?_ hVo.isClosed_compl
    intro z hz hzV
    exact hz (hfZero hzV)
  have hfSupport : tsupport f ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    by_contra hzR
    exact hfSupportV hz (hRV hzR)
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (ProperSpace.isCompact_closedBall (0 : ℂ) R)
    exact (subset_tsupport f).trans (hfSupport.trans Metric.ball_subset_closedBall)
  exact ⟨s, f, V, fun i ↦ (hs i).contDiffOn, htrans, hfSmooth, hfCompact,
    hfEq, hVo, hRV, hVU, hs0, hfSupport⟩

end SphereSixComplex.Analysis.CauchyGreen
