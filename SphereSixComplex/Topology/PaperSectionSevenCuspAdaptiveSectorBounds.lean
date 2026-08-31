module

public import SphereSixComplex.Topology.PaperSectionSevenCuspSignedCoverHeightCoordinateReduction

/-!
# Quantitative sector bounds for the adaptive cusp cover

The narrow sector control on the normalized modular cusp unit turns elementary angular
conditions on the cusp parameter into the two affine-height inequalities used by the
order-three/order-four cover.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Periods.ExactNormalizedModularJTau

variable {A : PaperAnalyticData}

/-- Multiplying a slightly narrowed right-facing sector by the controlled cusp unit remains
strictly inside the right-facing `45°` sector. -/
public theorem mul_mem_right_sector_of_narrow_right_sectors (q u : ℂ)
    (hqre : 0 < q.re) (hqsector : 50 * |q.im| ≤ 49 * q.re)
    (husector : 100 * |u.im| < u.re) :
    0 < (q * u).re ∧ |(q * u).im| < (q * u).re := by
  have hqsector' : |q.im| ≤ q.re := by
    have him := abs_nonneg q.im
    nlinarith
  have huim : 0 ≤ |u.im| := abs_nonneg _
  have husector' : |u.im| < u.re := by linarith
  have hure : 0 < u.re := lt_of_le_of_lt huim husector'
  have hre : 0 < (q * u).re :=
    mul_re_pos_of_right_sector q u hqre hqsector' husector'
  refine ⟨hre, ?_⟩
  rw [Complex.mul_im, Complex.mul_re]
  calc
    |q.re * u.im + q.im * u.re| ≤
        |q.re * u.im| + |q.im * u.re| := abs_add_le _ _
    _ = q.re * |u.im| + |q.im| * u.re := by
      rw [abs_mul, abs_mul, abs_of_pos hqre, abs_of_pos hure]
    _ < q.re * u.re - q.im * u.im := by
      have habsmul : q.im * u.im ≤ |q.im| * |u.im| := by
        calc
          q.im * u.im ≤ |q.im * u.im| := le_abs_self _
          _ = |q.im| * |u.im| := abs_mul _ _
      nlinarith [mul_nonneg hqre.le huim,
        mul_nonneg (abs_nonneg q.im) hure.le,
        mul_nonneg (abs_nonneg q.im) huim]

/-- On the selected cusp collar, a parameter in the narrowed right sector has normalized
reciprocal height above `1/3`. -/
public theorem one_third_lt_actualCuspReciprocalProduct_re
    (q : ℂ) (hq : ‖q‖ < A.actualPuncturedCuspWitness.localWitness.radius)
    (hqre : 0 < q.re) (hqsector : 50 * |q.im| ≤ 49 * q.re) :
    (1 / 3 : ℝ) <
      (q * A.actualNormalizedModularJUniformization.cusp.cuspUnit q)⁻¹.re := by
  let u := A.actualNormalizedModularJUniformization.cusp.cuspUnit q
  have hproduct := mul_mem_right_sector_of_narrow_right_sectors q u hqre hqsector
    (A.actualPuncturedCuspWitness_cuspUnit_narrow_right_sector q hq)
  exact one_third_lt_inv_re_of_norm_lt_half_of_right_sector _ hproduct.1 hproduct.2
    (A.actualPuncturedCuspWitness_cuspProduct_norm_lt_half q hq)

/-- On the selected cusp collar, a parameter in the left-facing `45°` sector has normalized
reciprocal height below `2/3`. -/
public theorem actualCuspReciprocalProduct_re_lt_two_thirds
    (q : ℂ) (hq : ‖q‖ < A.actualPuncturedCuspWitness.localWitness.radius)
    (hqre : q.re < 0) (hqsector : |q.im| ≤ -q.re) :
    (q * A.actualNormalizedModularJUniformization.cusp.cuspUnit q)⁻¹.re <
      (2 / 3 : ℝ) := by
  let u := A.actualNormalizedModularJUniformization.cusp.cuspUnit q
  have hproduct : (q * u).re < 0 :=
    mul_re_neg_of_left_sector q u hqre hqsector
      (A.actualPuncturedCuspWitness_cuspUnit_right_sector q hq)
  have hinv : (q * u)⁻¹.re < 0 := inv_re_neg_of_re_neg _ hproduct
  dsimp only [u] at hinv
  linarith

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
