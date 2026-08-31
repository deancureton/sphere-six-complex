module

public import SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau

/-!
# Quantitative control of the normalized modular `J` cusp unit

The explicit cusp unit tends to the positive real number `1728`.  This gives a smaller cusp
disc on which its real part stays uniformly positive.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Periods.ExactNormalizedModularJTau

/-- Multiplication preserves the sign of a right-facing `45°` sector. -/
public theorem mul_re_pos_of_right_sector (q u : ℂ)
    (hqre : 0 < q.re) (hqsector : |q.im| ≤ q.re)
    (husector : |u.im| < u.re) :
    0 < (q * u).re := by
  rw [Complex.mul_re]
  apply sub_pos.mpr
  calc
    q.im * u.im ≤ |q.im * u.im| := le_abs_self _
    _ = |q.im| * |u.im| := abs_mul _ _
    _ ≤ q.re * |u.im| := mul_le_mul_of_nonneg_right hqsector (abs_nonneg _)
    _ < q.re * u.re := mul_lt_mul_of_pos_left husector hqre

/-- Multiplication sends the opposite `45°` sector to the left half-plane. -/
public theorem mul_re_neg_of_left_sector (q u : ℂ)
    (hqre : q.re < 0) (hqsector : |q.im| ≤ -q.re)
    (husector : |u.im| < u.re) :
    (q * u).re < 0 := by
  have hneg : 0 < ((-q) * u).re :=
    mul_re_pos_of_right_sector (-q) u (by simpa using neg_pos.mpr hqre)
      (by simpa using hqsector) husector
  simpa using hneg

/-- A factor in a `2 : 1` right sector times a factor in the much narrower cusp-unit sector
still lies in the right `45°` sector. -/
public theorem mul_mem_right_sector_of_narrow_right_sector (q u : ℂ)
    (hqre : 0 < q.re) (hqsector : 2 * |q.im| ≤ q.re)
    (husector : 100 * |u.im| < u.re) :
    0 < (q * u).re ∧ |(q * u).im| < (q * u).re := by
  have hure : 0 < u.re := by
    nlinarith [abs_nonneg u.im]
  have hqim : |q.im| ≤ q.re / 2 := by linarith
  have huim : |u.im| < u.re / 100 := by linarith
  have hcross : q.im * u.im < q.re * u.re / 200 := by
    calc
      q.im * u.im ≤ |q.im * u.im| := le_abs_self _
      _ = |q.im| * |u.im| := abs_mul _ _
      _ ≤ (q.re / 2) * |u.im| :=
        mul_le_mul_of_nonneg_right hqim (abs_nonneg _)
      _ < (q.re / 2) * (u.re / 100) :=
        mul_lt_mul_of_pos_left huim (by positivity)
      _ = q.re * u.re / 200 := by ring
  have hreLower : q.re * u.re * 199 / 200 < (q * u).re := by
    rw [Complex.mul_re]
    nlinarith
  have himUpper : |(q * u).im| < q.re * u.re * 51 / 100 := by
    rw [Complex.mul_im]
    calc
      |q.re * u.im + q.im * u.re| ≤
          |q.re * u.im| + |q.im * u.re| := abs_add_le _ _
      _ = q.re * |u.im| + |q.im| * u.re := by
        rw [abs_mul, abs_mul, abs_of_pos hqre, abs_of_pos hure]
      _ < q.re * (u.re / 100) + (q.re / 2) * u.re := by
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left huim hqre)
          (mul_le_mul_of_nonneg_right hqim hure.le)
      _ = q.re * u.re * 51 / 100 := by ring
  constructor
  · exact (by positivity : 0 < q.re * u.re * 199 / 200).trans hreLower
  · have hac : 0 < q.re * u.re := mul_pos hqre hure
    have hmid : q.re * u.re * 51 / 100 < (q * u).re := by
      nlinarith [hreLower]
    exact himUpper.trans hmid

public theorem inv_re_pos_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    0 < z⁻¹.re := by
  have hzne : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr hzne)

public theorem inv_re_neg_of_re_neg (z : ℂ) (hz : z.re < 0) :
    z⁻¹.re < 0 := by
  have hzne : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  rw [Complex.inv_re]
  exact div_neg_of_neg_of_pos hz (Complex.normSq_pos.mpr hzne)

/-- A small complex number in the right `45°` sector has reciprocal real part bigger than
`1/3`. -/
public theorem one_third_lt_inv_re_of_norm_lt_half_of_right_sector
    (z : ℂ) (hre : 0 < z.re) (hsector : |z.im| < z.re)
    (hnorm : ‖z‖ < (1 / 2 : ℝ)) :
    (1 / 3 : ℝ) < z⁻¹.re := by
  have hreNorm : z.re ≤ ‖z‖ :=
    (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have hreHalf : z.re < 1 / 2 := hreNorm.trans_lt hnorm
  have himsq : z.im ^ 2 < z.re ^ 2 := by
    have hsquare := mul_self_lt_mul_self (abs_nonneg z.im) hsector
    calc
      z.im ^ 2 = |z.im| ^ 2 := (sq_abs z.im).symm
      _ < z.re ^ 2 := by simpa only [pow_two] using hsquare
  have hnormSq : Complex.normSq z < 3 * z.re := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hzne : z ≠ 0 := by
    intro h
    subst z
    norm_num at hre
  rw [Complex.inv_re,
    div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) (Complex.normSq_pos.mpr hzne)]
  nlinarith

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

/-- On some smaller cusp disc, the unit is within `864` of its constant term. -/
public theorem exists_normalizedModularJCuspUnit_close_radius :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball (0 : ℂ) r,
      dist (normalizedModularJCuspUnit q) 1728 < 864 :=
  exists_normalizedModularJCuspUnit_close_radius_of_pos (by norm_num)

/-- After shrinking the cusp disc, the unit has uniformly positive real part. -/
public theorem exists_normalizedModularJCuspUnit_re_lower_bound :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball (0 : ℂ) r,
      864 < (normalizedModularJCuspUnit q).re := by
  rcases exists_normalizedModularJCuspUnit_close_radius with ⟨r, hr, hclose⟩
  refine ⟨r, hr, ?_⟩
  intro q hq
  have hre : |(normalizedModularJCuspUnit q).re - 1728| < 864 := by
    calc
      |(normalizedModularJCuspUnit q).re - 1728| =
          |(normalizedModularJCuspUnit q - 1728).re| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_re_le_norm _
      _ = dist (normalizedModularJCuspUnit q) 1728 :=
        (dist_eq_norm (normalizedModularJCuspUnit q) 1728).symm
      _ < 864 := hclose q hq
  rw [abs_lt] at hre
  linarith

/-- On a smaller cusp disc, the unit lies strictly inside the right-facing `45°` sector. -/
public theorem exists_normalizedModularJCuspUnit_right_sector :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball (0 : ℂ) r,
      |(normalizedModularJCuspUnit q).im| <
        (normalizedModularJCuspUnit q).re := by
  rcases exists_normalizedModularJCuspUnit_close_radius with ⟨r, hr, hclose⟩
  refine ⟨r, hr, ?_⟩
  intro q hq
  have him : |(normalizedModularJCuspUnit q).im| < 864 := by
    calc
      |(normalizedModularJCuspUnit q).im| =
          |(normalizedModularJCuspUnit q - 1728).im| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_im_le_norm _
      _ = dist (normalizedModularJCuspUnit q) 1728 :=
        (dist_eq_norm (normalizedModularJCuspUnit q) 1728).symm
      _ < 864 := hclose q hq
  have hre : |(normalizedModularJCuspUnit q).re - 1728| < 864 := by
    calc
      |(normalizedModularJCuspUnit q).re - 1728| =
          |(normalizedModularJCuspUnit q - 1728).re| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_re_le_norm _
      _ = dist (normalizedModularJCuspUnit q) 1728 :=
        (dist_eq_norm (normalizedModularJCuspUnit q) 1728).symm
      _ < 864 := hclose q hq
  rw [abs_lt] at hre
  linarith

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

/-- The same cusp disc also carries a uniform norm bound for the unit. -/
public theorem exists_normalizedModularJCuspUnit_right_sector_norm_bound :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball (0 : ℂ) r,
      |(normalizedModularJCuspUnit q).im| <
          (normalizedModularJCuspUnit q).re ∧
        ‖normalizedModularJCuspUnit q‖ < 2592 := by
  rcases exists_normalizedModularJCuspUnit_close_radius with ⟨r, hr, hclose⟩
  refine ⟨r, hr, ?_⟩
  intro q hq
  have hdist := hclose q hq
  have hnormSub : ‖normalizedModularJCuspUnit q - 1728‖ < 864 := by
    rwa [dist_eq_norm] at hdist
  have him : |(normalizedModularJCuspUnit q).im| < 864 := by
    calc
      |(normalizedModularJCuspUnit q).im| =
          |(normalizedModularJCuspUnit q - 1728).im| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_im_le_norm _
      _ < 864 := hnormSub
  have hre : |(normalizedModularJCuspUnit q).re - 1728| < 864 := by
    calc
      |(normalizedModularJCuspUnit q).re - 1728| =
          |(normalizedModularJCuspUnit q - 1728).re| := by norm_num
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ := Complex.abs_re_le_norm _
      _ < 864 := hnormSub
  have hunitNorm : ‖normalizedModularJCuspUnit q‖ < 2592 := by
    calc
      ‖normalizedModularJCuspUnit q‖ =
          ‖(normalizedModularJCuspUnit q - 1728) + 1728‖ := by ring_nf
      _ ≤ ‖normalizedModularJCuspUnit q - 1728‖ + ‖(1728 : ℂ)‖ := norm_add_le _ _
      _ < 2592 := by norm_num; linarith
  rw [abs_lt] at hre
  exact ⟨by linarith, hunitNorm⟩

end SphereSixComplex.Periods.ExactNormalizedModularJTau
