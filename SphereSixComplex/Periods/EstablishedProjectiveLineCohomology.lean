module

public import SphereSixComplex.Periods.ProjectiveLineTorsors
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Established analytic Cech vanishing on the projective line

The Laurent-polynomial splittings are proved in `ProjectiveLineTorsors`.  Passing from Laurent
polynomials to arbitrary holomorphic functions on `ℂˣ` is the classical Laurent-series theorem.
We isolate exactly the two resulting Cech-surjectivity statements used for `O(-1)` and `O`.
-/

open Filter Metric Set
open scoped ENNReal Manifold NNReal Topology

noncomputable section

namespace SphereSixComplex.Periods

/-- A complex-valued function is holomorphic on the punctured plane. -/
public def HolomorphicOnPuncturedPlane (f : ℂ → ℂ) : Prop :=
  ∀ z, z ≠ 0 → MDiffAt f z

/-- An entire function is holomorphic on the punctured plane. -/
public theorem holomorphicOnPuncturedPlane_of_mdiff (f : ℂ → ℂ) (hf : MDiff f) :
    HolomorphicOnPuncturedPlane f :=
  fun z _ ↦ hf z

/-! ## Bridge to the manifold spelling used in the project -/

private theorem mdiffAt_complex_iff_differentiableAt {f : ℂ → ℂ} {z : ℂ} :
    MDiffAt f z ↔ DifferentiableAt ℂ f z := by
  exact (mdifferentiableAt_iff_differentiableAt (𝕜 := ℂ) (E := ℂ) (E' := ℂ))

private theorem mdiff_complex_iff_differentiable {f : ℂ → ℂ} :
    MDiff f ↔ Differentiable ℂ f := by
  exact (mdifferentiable_iff_differentiable (𝕜 := ℂ) (E := ℂ) (E' := ℂ))

/-- The calculus spelling of holomorphicity on `ℂˣ`. -/
private def DifferentiableOnPuncturedPlane (f : ℂ → ℂ) : Prop :=
  ∀ z, z ≠ 0 → DifferentiableAt ℂ f z

/-- Cauchy's nonnegative-coefficient power series, initially taken on the unit circle. -/
private def positiveSeries (f : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries f 0 1

/-- The Cauchy power series of a function holomorphic on `ℂˣ` is independent of the
positive radius used to define its coefficients.  This is the key coefficient-independence fact
behind Laurent expansion on the punctured plane. -/
private theorem cauchyPowerSeries_zero_eq_of_pos_of_le
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) :
    cauchyPowerSeries f 0 r = cauchyPowerSeries f 0 R := by
  funext n
  unfold cauchyPowerSeries
  congr 1
  have hzero : ∀ z ∈ closedBall (0 : ℂ) R \ ball 0 r, z ≠ 0 := by
    intro z hz h
    subst z
    exact hz.2 (mem_ball_self hr)
  have hfc : ContinuousOn f (closedBall (0 : ℂ) R \ ball 0 r) := by
    intro z hz
    exact (hf z (hzero z hz)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (fun z : ℂ ↦ (z - 0)⁻¹ ^ n * f z)
      (closedBall (0 : ℂ) R \ ball 0 r) := by
    exact (((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz h ↦ hzero z hz (sub_eq_zero.mp h))).pow n).mul hfc
  have hgd : ∀ z ∈ ball (0 : ℂ) R \ closedBall 0 r,
      DifferentiableAt ℂ (fun z : ℂ ↦ (z - 0)⁻¹ ^ n * f z) z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.2 (mem_closedBall_self hr.le)
    have hsub : DifferentiableAt ℂ (fun w : ℂ ↦ w - 0) z := by fun_prop
    have hinv : DifferentiableAt ℂ (fun w : ℂ ↦ (w - 0)⁻¹) z :=
      hsub.inv (sub_ne_zero.mpr hz0)
    exact (hinv.pow n).mul (hf z hz0)
  have hIntegral :
      (∮ z in C(0, r), (z - 0)⁻¹ ^ n • (z - 0)⁻¹ • f z) =
        ∮ z in C(0, R), (z - 0)⁻¹ ^ n • (z - 0)⁻¹ • f z := by
    simpa only [smul_eq_mul, sub_zero, mul_comm, mul_left_comm, mul_assoc] using
      (Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
        hr hle countable_empty hgc (by simpa only [sdiff_empty] using hgd)).symm
  rw [hIntegral]

private theorem cauchyPowerSeries_zero_eq_of_pos
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    cauchyPowerSeries f 0 r = cauchyPowerSeries f 0 R := by
  rcases le_total r R with hle | hle
  · exact cauchyPowerSeries_zero_eq_of_pos_of_le hf hr hle
  · exact (cauchyPowerSeries_zero_eq_of_pos_of_le hf hR hle).symm

/-- The nonnegative Cauchy series has infinite radius of convergence. -/
private theorem positiveSeries_radius_eq_top
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f) :
    (positiveSeries f).radius = ∞ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro R
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  have hRpos : 0 < (R : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hR)
  rw [positiveSeries, cauchyPowerSeries_zero_eq_of_pos hf one_pos hRpos]
  exact le_radius_cauchyPowerSeries f 0 R

/-- The entire function consisting of the nonnegative Laurent coefficients of `f`. -/
private def positivePart (f : ℂ → ℂ) : ℂ → ℂ :=
  (positiveSeries f).sum

private theorem differentiable_positivePart
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f) :
    Differentiable ℂ (positivePart f) := by
  have hr : 0 < (positiveSeries f).radius := by
    rw [positiveSeries_radius_eq_top hf]
    exact ENNReal.coe_lt_top
  have hd := (positiveSeries f).hasFPowerSeriesOnBall hr |>.differentiableOn
  rw [positiveSeries_radius_eq_top hf, Metric.eball_top] at hd
  exact differentiableOn_univ.mp hd

private theorem continuousOn_sphere_of_punctured
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {R : ℝ} (hR : 0 < R) : ContinuousOn f (sphere 0 R) := by
  intro z hz
  apply (hf z ?_).continuousAt.continuousWithinAt
  intro h
  subst z
  have h0R : (0 : ℝ) = R := by simpa [mem_sphere_iff_norm] using hz
  exact hR.ne' h0R.symm

private theorem circleIntegrable_of_punctured
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {R : ℝ} (hR : 0 < R) : CircleIntegrable f 0 R :=
  (continuousOn_sphere_of_punctured hf hR).circleIntegrable hR.le

private theorem continuousOn_sub_inv_sphere
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≠ R) :
    ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere 0 R) := by
  apply (continuousOn_id.sub continuousOn_const).inv₀
  intro w hw hwz
  have : w = z := sub_eq_zero.mp hwz
  subst w
  apply hz
  simpa [mem_sphere_iff_norm] using hw

private theorem circleIntegrable_cauchyKernel_mul
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≠ R) :
    CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ * f w) 0 R :=
  ((continuousOn_sub_inv_sphere hz).mul
    (continuousOn_sphere_of_punctured hf hR)).circleIntegrable hR.le

/-- On a disk bounded by a positive circle, `positivePart` is the corresponding normalized
Cauchy integral. -/
private theorem positivePart_eq_cauchyIntegral
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    positivePart f z =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ w in C(0, R), (w - z)⁻¹ * f w := by
  unfold positivePart positiveSeries
  rw [cauchyPowerSeries_zero_eq_of_pos hf one_pos hR]
  simpa only [smul_eq_mul, zero_add] using
    sum_cauchyPowerSeries_eq_integral (circleIntegrable_of_punctured hf hR) hz

private theorem circleIntegral_sub_inv_eq_zero_of_lt_norm
    {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : r < ‖z‖) :
    (∮ w in C(0, r), (w - z)⁻¹) = 0 := by
  have hne : ∀ w ∈ closedBall (0 : ℂ) r, w - z ≠ 0 := by
    intro w hw hwz
    have : w = z := sub_eq_zero.mp hwz
    subst w
    exact (not_le_of_gt hz) (by simpa [mem_closedBall_iff_norm] using hw)
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ hne
  · intro w hw
    have hsub : DifferentiableAt ℂ (fun u : ℂ ↦ u - z) w := by fun_prop
    exact hsub.inv (hne w (ball_subset_closedBall hw.1))

private theorem circleIntegral_dslope_eq_on_annulus
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) {z : ℂ}
    (hzr : r < ‖z‖) (hzR : ‖z‖ < R) :
    (∮ w in C(0, R), dslope f z w) = ∮ w in C(0, r), dslope f z w := by
  let S : Set ℂ := closedBall 0 R \ ball 0 r
  let U : Set ℂ := ball 0 R \ closedBall 0 r
  have hUopen : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hzU : z ∈ U := by
    constructor
    · simpa [U, mem_ball_iff_norm] using hzR
    · simpa [U, mem_closedBall_iff_norm, not_le] using hzr
  have hUS : U ⊆ S := by
    rintro w ⟨hwR, hwr⟩
    exact ⟨ball_subset_closedBall hwR, fun h ↦ hwr (ball_subset_closedBall h)⟩
  have hSnhds : S ∈ nhds z :=
    mem_of_superset (hUopen.mem_nhds hzU) hUS
  have hzeroS : ∀ w ∈ S, w ≠ 0 := by
    intro w hw h
    subst w
    exact hw.2 (mem_ball_self hr)
  have hfS : DifferentiableOn ℂ f S := by
    intro w hw
    exact (hf w (hzeroS w hw)).differentiableWithinAt
  have hds : DifferentiableOn ℂ (dslope f z) S :=
    (Complex.differentiableOn_dslope hSnhds).mpr hfS
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hle countable_empty hds.continuousOn
  intro w hw
  apply hds.differentiableAt
  exact mem_of_superset (hUopen.mem_nhds hw.1) hUS

/-- The normalized outer Cauchy integral minus the inner one is the value of the holomorphic
function at a point of the intervening annulus. -/
private theorem normalized_cauchyIntegral_sub_eq
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) {z : ℂ}
    (hzr : r < ‖z‖) (hzR : ‖z‖ < R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ w in C(0, R), (w - z)⁻¹ * f w) -
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ w in C(0, r), (w - z)⁻¹ * f w) = f z := by
  have hzOuter : z ∈ ball (0 : ℂ) R := by
    simpa [mem_ball_iff_norm] using hzR
  have hzRne : ‖z‖ ≠ R := ne_of_lt hzR
  have hzrne : ‖z‖ ≠ r := ne_of_gt hzr
  have hKOuter : CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ * f w) 0 R :=
    circleIntegrable_cauchyKernel_mul hf (hr.trans_le hle) hzRne
  have hKInner : CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ * f w) 0 r :=
    circleIntegrable_cauchyKernel_mul hf hr hzrne
  have hCOuter : CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ * f z) 0 R :=
    ((continuousOn_sub_inv_sphere hzRne).mul
      continuousOn_const).circleIntegrable (hr.trans_le hle).le
  have hCInner : CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ * f z) 0 r :=
    ((continuousOn_sub_inv_sphere hzrne).mul continuousOn_const).circleIntegrable hr.le
  have hEqOuter : EqOn (dslope f z)
      (fun w : ℂ ↦ (w - z)⁻¹ * f w - (w - z)⁻¹ * f z) (sphere 0 R) := by
    intro w hw
    have hwz : w ≠ z := sphere_disjoint_ball.ne_of_mem hw hzOuter
    rw [dslope_of_ne f hwz]
    simp only [slope, vsub_eq_sub, smul_eq_mul, mul_sub]
  have hEqInner : EqOn (dslope f z)
      (fun w : ℂ ↦ (w - z)⁻¹ * f w - (w - z)⁻¹ * f z) (sphere 0 r) := by
    intro w hw
    have hwz : w ≠ z := by
      intro h
      subst w
      exact hzrne (by simpa [mem_sphere_iff_norm] using hw)
    rw [dslope_of_ne f hwz]
    simp only [slope, vsub_eq_sub, smul_eq_mul, mul_sub]
  have hDOuter :
      (∮ w in C(0, R), dslope f z w) =
        (∮ w in C(0, R), (w - z)⁻¹ * f w) -
          ∮ w in C(0, R), (w - z)⁻¹ * f z := by
    calc
      _ = ∮ w in C(0, R),
          ((w - z)⁻¹ * f w - (w - z)⁻¹ * f z) :=
        circleIntegral.integral_congr (hr.trans_le hle).le hEqOuter
      _ = _ := circleIntegral.integral_sub hKOuter hCOuter
  have hDInner :
      (∮ w in C(0, r), dslope f z w) =
        (∮ w in C(0, r), (w - z)⁻¹ * f w) -
          ∮ w in C(0, r), (w - z)⁻¹ * f z := by
    calc
      _ = ∮ w in C(0, r),
          ((w - z)⁻¹ * f w - (w - z)⁻¹ * f z) :=
        circleIntegral.integral_congr hr.le hEqInner
      _ = _ := circleIntegral.integral_sub hKInner hCInner
  have hCOuterValue :
      (∮ w in C(0, R), (w - z)⁻¹ * f z) =
        (2 * Real.pi * Complex.I : ℂ) * f z := by
    calc
      _ = (∮ w in C(0, R), (w - z)⁻¹) * f z := by
        simpa only [smul_eq_mul] using
          circleIntegral.integral_smul_const (fun w : ℂ ↦ (w - z)⁻¹) (f z) 0 R
      _ = _ := by rw [circleIntegral.integral_sub_inv_of_mem_ball hzOuter]
  have hCInnerValue :
      (∮ w in C(0, r), (w - z)⁻¹ * f z) = 0 := by
    calc
      _ = (∮ w in C(0, r), (w - z)⁻¹) * f z := by
        simpa only [smul_eq_mul] using
          circleIntegral.integral_smul_const (fun w : ℂ ↦ (w - z)⁻¹) (f z) 0 r
      _ = 0 := by rw [circleIntegral_sub_inv_eq_zero_of_lt_norm hr.le hzr, zero_mul]
  have hD := circleIntegral_dslope_eq_on_annulus hf hr hle hzr hzR
  rw [hCOuterValue] at hDOuter
  rw [hCInnerValue, sub_zero] at hDInner
  have hJump :
      (∮ w in C(0, R), (w - z)⁻¹ * f w) -
          (∮ w in C(0, r), (w - z)⁻¹ * f w) =
        (2 * Real.pi * Complex.I : ℂ) * f z := by
    have hOuterValue :
        (∮ w in C(0, R), (w - z)⁻¹ * f w) =
          (∮ w in C(0, R), dslope f z w) +
            (2 * Real.pi * Complex.I : ℂ) * f z := by
      calc
        _ = ((∮ w in C(0, R), (w - z)⁻¹ * f w) -
              (2 * Real.pi * Complex.I : ℂ) * f z) +
            (2 * Real.pi * Complex.I : ℂ) * f z := by ring
        _ = _ := by rw [← hDOuter]
    rw [hOuterValue, ← hDInner, hD]
    ring
  rw [← mul_sub, hJump]
  exact inv_mul_cancel_left₀ Complex.two_pi_I_ne_zero (f z)

/-- Outside a positive circle, the negative Laurent tail is its normalized Cauchy integral. -/
private theorem positivePart_sub_eq_inner_cauchyIntegral
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hzr : r < ‖z‖) :
    positivePart f z - f z =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ w in C(0, r), (w - z)⁻¹ * f w := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hzR : ‖z‖ < R := by simp [R]
  have hrR : r ≤ R := (hzr.trans hzR).le
  rw [positivePart_eq_cauchyIntegral hf hR hzR]
  linear_combination normalized_cauchyIntegral_sub_eq hf hr hrR hzr hzR

/-- The negative Laurent tail, expressed in the coordinate at infinity away from its origin. -/
private def negativePartRaw (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  positivePart f w⁻¹ - f w⁻¹

private theorem differentiableAt_negativePartRaw
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f)
    {w : ℂ} (hw : w ≠ 0) : DifferentiableAt ℂ (negativePartRaw f) w := by
  have hinv : DifferentiableAt ℂ (fun z : ℂ ↦ z⁻¹) w := differentiableAt_inv hw
  have hpos := (differentiable_positivePart hf w⁻¹).comp w hinv
  have hfinv : w⁻¹ ≠ 0 := inv_ne_zero hw
  exact hpos.sub ((hf w⁻¹ hfinv).comp w hinv)

private theorem bddAbove_negativePartRaw_half
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f) :
    BddAbove (norm ∘ negativePartRaw f ''
      (closedBall (0 : ℂ) (2 : ℝ)⁻¹ \ {0})) := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).bddAbove_image
    (continuousOn_sphere_of_punctured hf one_pos).norm
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right M 0
  refine ⟨‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (2 * Real.pi * C), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  change ‖negativePartRaw f q‖ ≤ _
  have hq0 : q ≠ 0 := by simpa using hq.2
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hqnorm : ‖q‖ ≤ (2 : ℝ)⁻¹ := by
    simpa [mem_closedBall_iff_norm] using hq.1
  have hzTwo : 2 ≤ ‖q⁻¹‖ := by
    rw [norm_inv]
    calc
      2 ≤ 1 * ‖q‖⁻¹ := (le_mul_inv_iff₀ hqpos).2 (by nlinarith)
      _ = ‖q‖⁻¹ := one_mul _
  have hzOne : 1 < ‖q⁻¹‖ := one_lt_two.trans_le hzTwo
  have hrepr : negativePartRaw f q =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ w in C(0, 1), (w - q⁻¹)⁻¹ * f w := by
    simpa only [negativePartRaw] using
      positivePart_sub_eq_inner_cauchyIntegral hf one_pos hzOne
  have hpoint : ∀ w ∈ sphere (0 : ℂ) 1, ‖(w - q⁻¹)⁻¹ * f w‖ ≤ C := by
    intro w hw
    have hwnorm : ‖w‖ = 1 := by simpa [mem_sphere_iff_norm] using hw
    have hden : 1 ≤ ‖w - q⁻¹‖ := by
      calc
        1 ≤ ‖q⁻¹‖ - ‖w‖ := by rw [hwnorm]; linarith
        _ ≤ ‖q⁻¹ - w‖ := norm_sub_norm_le _ _
        _ = ‖w - q⁻¹‖ := norm_sub_rev _ _
    have hinv : ‖(w - q⁻¹)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
    have hfwM : ‖f w‖ ≤ M := by
      exact hM (mem_image_of_mem (norm ∘ f) hw)
    have hfw : ‖f w‖ ≤ C := hfwM.trans (le_max_left M 0)
    calc
      ‖(w - q⁻¹)⁻¹ * f w‖ = ‖(w - q⁻¹)⁻¹‖ * ‖f w‖ := norm_mul _ _
      _ ≤ 1 * C := mul_le_mul hinv hfw (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hIntegral := circleIntegral.norm_integral_le_of_norm_le_const
    (show (0 : ℝ) ≤ 1 by norm_num) hpoint
  rw [hrepr, norm_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hIntegral (norm_nonneg (2 * Real.pi * Complex.I : ℂ)⁻¹)

/-- The negative Laurent tail, extended across the origin in the infinity coordinate. -/
private def negativePart (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (negativePartRaw f) 0
    (limUnder (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (negativePartRaw f))

private theorem differentiable_negativePart
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f) :
    Differentiable ℂ (negativePart f) := by
  let S : Set ℂ := closedBall 0 (2 : ℝ)⁻¹
  have hSnhds : S ∈ nhds (0 : ℂ) := by
    exact closedBall_mem_nhds 0 (by positivity)
  have hraw : DifferentiableOn ℂ (negativePartRaw f) (S \ {0}) := by
    intro w hw
    exact (differentiableAt_negativePartRaw hf (by simpa using hw.2)).differentiableWithinAt
  have hext : DifferentiableOn ℂ (negativePart f) S := by
    simpa only [negativePart] using
      Complex.differentiableOn_update_limUnder_of_bddAbove hSnhds hraw
        (bddAbove_negativePartRaw_half hf)
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · exact hext.differentiableAt hSnhds
  · apply (differentiableAt_negativePartRaw hf hw).congr_of_eventuallyEq
    have hmem : w ∈ ({0} : Set ℂ)ᶜ := by simpa
    filter_upwards [isOpen_compl_singleton.mem_nhds hmem] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simp only [negativePart, Function.update_of_ne hz0]

/-- Entire positive and negative Laurent tails split a function holomorphic on `ℂˣ`. -/
private theorem exists_entire_laurent_decomposition
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f) :
    ∃ fZero fInfinity : ℂ → ℂ,
      Differentiable ℂ fZero ∧ Differentiable ℂ fInfinity ∧
      ∀ z, z ≠ 0 → f z = fZero z - fInfinity z⁻¹ := by
  refine ⟨positivePart f, negativePart f, differentiable_positivePart hf,
    differentiable_negativePart hf, ?_⟩
  intro z hz
  simp [negativePart, negativePartRaw, inv_ne_zero hz]

/-- The `O(-1)` version follows by moving the constant term of the infinity tail to the zero
chart and factoring the remaining entire function through its divided slope at the origin. -/
private theorem exists_entire_laurent_decomposition_negOne
    {f : ℂ → ℂ} (hf : DifferentiableOnPuncturedPlane f) :
    ∃ fZero fInfinity : ℂ → ℂ,
      Differentiable ℂ fZero ∧ Differentiable ℂ fInfinity ∧
      ∀ z, z ≠ 0 → f z = fZero z - z⁻¹ * fInfinity z⁻¹ := by
  obtain ⟨fZero, gInfinity, hfZero, hgInfinity, hsplit⟩ :=
    exists_entire_laurent_decomposition hf
  let fInfinity : ℂ → ℂ := dslope gInfinity 0
  have hfInfinity : Differentiable ℂ fInfinity := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope univ_mem).mpr hgInfinity.differentiableOn
  refine ⟨fun z ↦ fZero z - gInfinity 0, fInfinity,
    hfZero.sub (by fun_prop), hfInfinity, ?_⟩
  intro z hz
  have hfactor : z⁻¹ * fInfinity z⁻¹ = gInfinity z⁻¹ - gInfinity 0 := by
    simpa only [fInfinity, sub_zero, smul_eq_mul] using
      sub_smul_dslope gInfinity 0 z⁻¹
  rw [hfactor, hsplit z hz]
  ring

/-! ## Cech exactness -/

/-- Analytic two-chart Cech exactness for `O(-1)` on `ℙ¹`.

The zero-chart coordinate is `z`; the infinity-chart coordinate is `z⁻¹`; and the infinity
section is expressed in the zero-chart frame by the transition factor `z⁻¹`. -/
public theorem establishedProjectiveLineCechNegOne
    (c : ℂ → ℂ) (hc : HolomorphicOnPuncturedPlane c) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        c z = fZero z - z⁻¹ * fInfinity (z⁻¹) := by
  have hc' : DifferentiableOnPuncturedPlane c := fun z hz ↦
    mdiffAt_complex_iff_differentiableAt.mp (hc z hz)
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    exists_entire_laurent_decomposition_negOne hc'
  exact ⟨fZero, fInfinity, mdiff_complex_iff_differentiable.mpr hfZero,
    mdiff_complex_iff_differentiable.mpr hfInfinity, hsplit⟩

/-- Analytic two-chart Cech exactness for the structure sheaf `O` on `ℙ¹`. -/
public theorem establishedProjectiveLineCechZero
    (c : ℂ → ℂ) (hc : HolomorphicOnPuncturedPlane c) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        c z = fZero z - fInfinity (z⁻¹) := by
  have hc' : DifferentiableOnPuncturedPlane c := fun z hz ↦
    mdiffAt_complex_iff_differentiableAt.mp (hc z hz)
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    exists_entire_laurent_decomposition hc'
  exact ⟨fZero, fInfinity, mdiff_complex_iff_differentiable.mpr hfZero,
    mdiff_complex_iff_differentiable.mpr hfInfinity, hsplit⟩

/-- Two local `O(-1)` torsor sections with holomorphic overlap mismatch can be corrected by entire
functions so that they agree in the zero-chart frame. -/
public theorem exists_compatibleProjectiveLineNegOneAdjustments
    (sZero sInfinity : ℂ → ℂ)
    (hZero : HolomorphicOnPuncturedPlane sZero)
    (hInfinity : HolomorphicOnPuncturedPlane sInfinity) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        sZero z - fZero z =
          sInfinity z - z⁻¹ * fInfinity (z⁻¹) := by
  have hc : HolomorphicOnPuncturedPlane (fun z ↦ sZero z - sInfinity z) := by
    intro z hz
    exact (hZero z hz).sub (hInfinity z hz)
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechNegOne (fun z ↦ sZero z - sInfinity z) hc
  refine ⟨fZero, fInfinity, hfZero, hfInfinity, ?_⟩
  intro z hz
  have h := hsplit z hz
  linear_combination h

/-- Two local structure-sheaf torsor sections with holomorphic overlap mismatch can be corrected
to agree. -/
public theorem exists_compatibleProjectiveLineZeroAdjustments
    (sZero sInfinity : ℂ → ℂ)
    (hZero : HolomorphicOnPuncturedPlane sZero)
    (hInfinity : HolomorphicOnPuncturedPlane sInfinity) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        sZero z - fZero z = sInfinity z - fInfinity (z⁻¹) := by
  have hc : HolomorphicOnPuncturedPlane (fun z ↦ sZero z - sInfinity z) := by
    intro z hz
    exact (hZero z hz).sub (hInfinity z hz)
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechZero (fun z ↦ sZero z - sInfinity z) hc
  refine ⟨fZero, fInfinity, hfZero, hfInfinity, ?_⟩
  intro z hz
  have h := hsplit z hz
  linear_combination h

end SphereSixComplex.Periods
