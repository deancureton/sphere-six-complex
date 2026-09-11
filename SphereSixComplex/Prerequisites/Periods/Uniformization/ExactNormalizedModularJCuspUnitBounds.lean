module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.ExactNormalizedModularJTau

/-!
# Quantitative control of the normalized modular `J` cusp unit

The explicit cusp unit tends to the positive real number `1728`.  This gives a smaller cusp
disc on which its real part stays uniformly positive.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Periods.ExactNormalizedModularJTau







/-- The constant term of the normalized modular `J` cusp unit. -/
public theorem normalizedModularJCuspUnit_zero :
    normalizedModularJCuspUnit 0 = 1728 := by
  norm_num [normalizedModularJCuspUnit, discriminantCuspUnit, E₄_cuspFunction_zero]

/-- The normalized modular `J` cusp unit is continuous at the cusp. -/
public theorem continuousAt_normalizedModularJCuspUnit :
    ContinuousAt normalizedModularJCuspUnit 0 := by
  have hzero : (0 : ℂ) ∈ Metric.ball 0 exact_normalizedModularJ_cusp.cuspRadius := by
    simpa using exact_normalizedModularJ_cusp.cuspRadius_pos
  exact (exact_normalizedModularJ_cusp.cuspUnit_holomorphic 0 hzero).continuousAt

/-- On a sufficiently small cusp disc, the unit is uniformly close to its constant term. -/
public theorem exists_normalizedModularJCuspUnit_close_radius_of_pos
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball (0 : ℂ) r,
      dist (normalizedModularJCuspUnit q) 1728 < ε := by
  have hevent : ∀ᶠ q in nhds (0 : ℂ),
      dist (normalizedModularJCuspUnit q) 1728 < ε := by
    have h := continuousAt_normalizedModularJCuspUnit.tendsto
    rw [normalizedModularJCuspUnit_zero] at h
    exact h.eventually (Metric.ball_mem_nhds (1728 : ℂ) hε)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨r, hr, hball⟩
  exact ⟨r, hr, fun q hq ↦ hball hq⟩




/-- The cusp unit can be confined to an arbitrarily tighter fixed sector around the positive
real axis; this concrete factor is convenient for the mapping-torus cover. -/
public theorem exists_normalizedModularJCuspUnit_narrow_right_sector :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball (0 : ℂ) r,
      100 * |(normalizedModularJCuspUnit q).im| <
        (normalizedModularJCuspUnit q).re := by
  rcases exists_normalizedModularJCuspUnit_close_radius_of_pos (by norm_num : (0 : ℝ) < 8)
    with ⟨r, hr, hclose⟩
  refine ⟨r, hr, ?_⟩
  intro q hq
  have hnorm : ‖normalizedModularJCuspUnit q - 1728‖ < 8 := by
    simpa [dist_eq_norm] using hclose q hq
  have him : |(normalizedModularJCuspUnit q).im| < 8 := by
    calc
      |(normalizedModularJCuspUnit q).im| =
          |(normalizedModularJCuspUnit q - 1728).im| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_im_le_norm _
      _ < 8 := hnorm
  have hre : |(normalizedModularJCuspUnit q).re - 1728| < 8 := by
    calc
      |(normalizedModularJCuspUnit q).re - 1728| =
          |(normalizedModularJCuspUnit q - 1728).re| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_re_le_norm _
      _ < 8 := hnorm
  rw [abs_lt] at hre
  nlinarith


end SphereSixComplex.Periods.ExactNormalizedModularJTau
