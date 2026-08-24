module

public import TauCeti.Analysis.Complex.BranchLogRoot
import all TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import all TauCeti.Analysis.Complex.Conformal.LocalDegree
public import Mathlib.Analysis.Normed.Module.Connected
import all Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

noncomputable section

open Complex Metric Filter Topology

namespace TauCeti

/-- A nonzero analytic germ has a holomorphic `n`-th root on a sufficiently small disc. -/
private lemma exists_ball_pow_eq_of_ne_zero_current
    {A : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hA : AnalyticAt ℂ A z₀)
    (h0 : A z₀ ≠ 0) (hn : n ≠ 0) :
    ∃ r > 0, ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball z₀ r) ∧ ∀ z ∈ ball z₀ r, h z ^ n = A z := by
  have hloc : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ A z ∧ A z ≠ 0 :=
    hA.eventually_analyticAt.and (hA.continuousAt.eventually_ne h0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  have hsc : IsSimplyConnected (ball z₀ r) := by
    have : ContractibleSpace (ball z₀ r) := Metric.contractibleSpace_ball hr
    exact SimplyConnectedSpace.ofContractible _
  have hAd : DifferentiableOn ℂ A (ball z₀ r) := fun z hz ↦
    ((hball (mem_ball.mp hz)).1.differentiableAt).differentiableWithinAt
  have hA0 : (0 : ℂ) ∉ A '' ball z₀ r := by
    rintro ⟨z, hz, hz0⟩
    exact (hball (mem_ball.mp hz)).2 hz0
  obtain ⟨h, hhd, hheq⟩ := exists_differentiableOn_pow_eq hsc isOpen_ball hAd hA0 hn
  exact ⟨r, hr, h, hhd, fun z hz ↦ hheq hz⟩

/-- Current-Tau-compatible local power normal form.  This is the minimal chart-producing result
from historical Tau commit `4a9f0b5...`; all imports above are from current Tau. -/
theorem exists_powerChart_of_analyticOrderAt
    {A : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hA : AnalyticAt ℂ A z₀)
    (hord : analyticOrderAt A z₀ = n) (hn : n ≠ 0) :
    ∃ r > 0, ∃ φ : ℂ → ℂ,
      DifferentiableOn ℂ φ (ball z₀ r) ∧ Set.InjOn φ (ball z₀ r) ∧
        φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧
          ∀ z ∈ ball z₀ r, A z = φ z ^ n := by
  obtain ⟨g, hg, hg0, hgeq⟩ := hA.analyticOrderAt_eq_natCast.mp hord
  obtain ⟨r₀, hr₀, hgball⟩ := Metric.eventually_nhds_iff.mp hgeq
  obtain ⟨r₁, hr₁, h, hhd, hheq⟩ :=
    exists_ball_pow_eq_of_ne_zero_current hg hg0 hn
  have hballnhds : ball z₀ r₁ ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hr₁)
  have hh0 : h z₀ ≠ 0 := by
    intro hz
    have hroot := hheq z₀ (mem_ball_self hr₁)
    rw [hz, zero_pow hn] at hroot
    exact hg0 hroot.symm
  set φ : ℂ → ℂ := fun z ↦ (z - z₀) * h z with hφdef
  have hφd : DifferentiableOn ℂ φ (ball z₀ r₁) := fun z hz ↦
    ((differentiableAt_id.sub_const z₀).mul
      (hhd.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have hφ₀ : φ z₀ = 0 := by simp [hφdef]
  have hφderiv : deriv φ z₀ = h z₀ := by
    have hd : HasDerivAt φ (1 * h z₀ + (z₀ - z₀) * deriv h z₀) z₀ :=
      ((hasDerivAt_id z₀).sub_const z₀).mul
        (hhd.differentiableAt hballnhds).hasDerivAt
    simpa using hd.deriv
  have hφne : deriv φ z₀ ≠ 0 := by rw [hφderiv]; exact hh0
  obtain ⟨V, hV, hVinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero (hφd.analyticAt hballnhds)).mpr hφne
  obtain ⟨r₂, hr₂, hr₂V⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨min r₀ (min r₁ r₂), lt_min hr₀ (lt_min hr₁ hr₂), φ,
    hφd.mono (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))), ?_, hφ₀,
    hφne, fun z hz ↦ ?_⟩
  · exact hVinj.mono
      ((ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hr₂V)
  · have hz₀ : dist z z₀ < r₀ := mem_ball.mp (ball_subset_ball (min_le_left _ _) hz)
    have hz₁ : z ∈ ball z₀ r₁ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz
    calc
      A z = (z - z₀) ^ n • g z := hgball hz₀
      _ = φ z ^ n := by rw [smul_eq_mul, ← hheq z hz₁, hφdef, mul_pow]


end TauCeti
