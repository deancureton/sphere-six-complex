/-
SPDX-License-Identifier: Apache-2.0
Adapted from the scalar Cauchy-Green development in plby/HopfProblem, Solution.lean,
commit 9ac8a456b526527837d7082ff775213ca8bc9809, lines 164622-164643,
164678-164687, and 164829-165163:
https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean
The source is released under Apache-2.0. This focused adaptation changes imports,
namespace, helper names and formatting; no sphere or period construction is imported.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open MeasureTheory Complex
open scoped Convolution ContDiff

namespace SphereSixComplex.Analysis.CauchyGreen

def dbarLinear : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) •
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

@[simp]
theorem dbarLinear_apply (L : ℂ →L[ℝ] ℂ) :
    dbarLinear L = (L 1 + Complex.I * L Complex.I) / 2 := by
  simp only [dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

theorem dbar_eq_dbarLinear (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = dbarLinear (fderiv ℝ f z) :=
  (dbarLinear_apply _).symm

theorem dbarLinear_complex_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear (c • L) = c * dbarLinear L := by
  simp only [dbarLinear_apply, smul_apply, smul_eq_mul]
  ring

theorem dbar_comp_const_sub {f : ℂ → ℂ} (a z : ℂ)
    (hf : DifferentiableAt ℝ f (a - z)) : dbar (fun w ↦ f (a - w)) z = -dbar f (a - z) := by
  have hi : HasFDerivAt (fun w : ℂ ↦ a - w) (-ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_sub a
  have he := (hf.hasFDerivAt.comp z hi).fderiv
  change fderiv ℝ (fun w ↦ f (a - w)) z = _ at he
  simp only [dbar, he, ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg]
  ring

theorem locallyIntegrable_complex_inv :
    MeasureTheory.LocallyIntegrable (fun z : ℂ ↦ z⁻¹) := by
  refine
    MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · filter_upwards with z
    simp only [norm_inv, Real.rpow_neg_one, one_mul, le_refl]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

def cauchyGreen (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, w⁻¹ * f (z - w)

theorem contDiff_cauchyGreen {n : ℕ∞} {f : ℂ → ℂ} (hf : ContDiff ℝ n f)
    (hcf : HasCompactSupport f) : ContDiff ℝ n (cauchyGreen f) := by
  change
    ContDiff ℝ n
      (fun z ↦ (1 / (Real.pi : ℂ)) * ((fun w : ℂ ↦ w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] f) z)
  exact
    contDiff_const.mul
      (hcf.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_complex_inv
        hf)

theorem hasFDerivAt_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    HasFDerivAt (cauchyGreen f)
      ((1 / (Real.pi : ℂ)) •
        ((fun w : ℂ ↦ w⁻¹) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ f) z)
      z := by
  convert!
    (hcf.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_complex_inv
          hf z).const_mul
      (1 / (Real.pi : ℂ)) using
    1

theorem dbarLinear_precompR_mul (a : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ a L) = a * dbarLinear L := by
  change dbarLinear (a • L) = a * dbarLinear L
  exact dbarLinear_complex_smul a L

theorem dbar_cauchyGreen_eq_cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : dbar (cauchyGreen f) z = cauchyGreen (dbar f) z := by
  have hi :
    MeasureTheory.Integrable
      (fun w : ℂ ↦ (ContinuousLinearMap.mul ℝ ℂ).precompR ℂ w⁻¹ (fderiv ℝ f (z - w))) :=
    (hcf.fderiv ℝ).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ)
      locallyIntegrable_complex_inv (hf.continuous_fderiv one_ne_zero) z
  rw [dbar_eq_dbarLinear, (hasFDerivAt_cauchyGreen hf hcf z).fderiv, dbarLinear_complex_smul,
    MeasureTheory.convolution_def, ← dbarLinear.integral_comp_comm hi]
  simp only [dbarLinear_precompR_mul, ← dbar_eq_dbarLinear, cauchyGreen]

def greenUnit (θ : ℝ) : ℂ :=
  circleMap 0 1 θ

theorem greenUnit_eq (θ : ℝ) :
    greenUnit θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  simp [greenUnit, circleMap, Complex.exp_mul_I]

@[simp]
theorem norm_greenUnit (θ : ℝ) : ‖greenUnit θ‖ = 1 := by simp [greenUnit]

theorem continuous_greenUnit : Continuous greenUnit := by
  exact continuous_circleMap 0 1

theorem polarCoord_symm_eq_greenUnit (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * greenUnit p.2 := by
  simp [Complex.polarCoord_symm_apply, greenUnit_eq]

theorem realLinear_apply_complex (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
  calc
    D z = D (z.re • (1 : ℂ) + z.im • Complex.I) := by
      congr 1
      simp [Complex.real_smul]
    _ = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.real_smul]

theorem polar_realLinear_identity (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z + Complex.I * D (Complex.I * z) = Star.star z * (D 1 + Complex.I * D Complex.I) := by
  have hc : Star.star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
  rw [realLinear_apply_complex D z, realLinear_apply_complex D (Complex.I * z), hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, MulZeroClass.zero_mul,
    one_mul, zero_sub, zero_add, Complex.ofReal_neg]
  ring_nf
  simp [Complex.I_sq]

def greenRadial (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (greenUnit p.2)

def greenAngular (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (Complex.I * greenUnit p.2)

theorem continuous_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenRadial φ) := by
  exact
    (hφ.continuous_fderiv_apply one_ne_zero).comp
      (((Complex.continuous_ofReal.comp continuous_fst).mul
            (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_greenUnit.comp continuous_snd))

theorem continuous_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenAngular φ) := by
  exact
    (hφ.continuous_fderiv_apply one_ne_zero).comp
      (((Complex.continuous_ofReal.comp continuous_fst).mul
            (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_const.mul (continuous_greenUnit.comp continuous_snd)))

theorem hasDerivAt_green_radial {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) : HasDerivAt (fun t : ℝ ↦ φ ((t : ℂ) * greenUnit θ)) (greenRadial φ (r, θ)) r := by
  apply (hφ _).hasFDerivAt.comp_hasDerivAt
  simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (greenUnit θ)

theorem hasDerivAt_green_angular {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ φ ((r : ℂ) * greenUnit t)) ((r : ℂ) * greenAngular φ (r, θ)) θ := by
  have hu : HasDerivAt greenUnit (Complex.I * greenUnit θ) θ := by
    change HasDerivAt (circleMap 0 1) (Complex.I * circleMap 0 1 θ) θ
    simpa [mul_comm] using hasDerivAt_circleMap 0 1 θ
  have hd := (hφ _).hasFDerivAt.comp_hasDerivAt θ (hu.const_mul (r : ℂ))
  simpa only [Function.comp_def, ← Complex.real_smul, map_smul, greenAngular] using hd

theorem integral_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (R θ : ℝ) :
    (∫ r in 0..R, greenRadial φ (r, θ)) = φ ((R : ℂ) * greenUnit θ) - φ 0 := by
  have hint :
    IntervalIntegrable (fun r ↦ greenRadial φ (r, θ)) MeasureTheory.MeasureSpace.volume 0 R :=
    ((continuous_greenRadial hφ).comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      _ _
  simpa using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ ↦ hasDerivAt_green_radial (hφ.differentiable one_ne_zero) r θ) hint

theorem integral_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {r : ℝ}
    (hr : r ≠ 0) : (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
  have hint :
    IntervalIntegrable (fun θ ↦ (r : ℂ) * greenAngular φ (r, θ))
      MeasureTheory.MeasureSpace.volume (-Real.pi) Real.pi :=
    (continuous_const.mul
          ((continuous_greenAngular hφ).comp
            (continuous_const.prodMk continuous_id))).intervalIntegrable
      _ _
  have heq :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ ↦ hasDerivAt_green_angular (hφ.differentiable one_ne_zero) r θ) hint
  have hend : greenUnit Real.pi = greenUnit (-Real.pi) := by simp [greenUnit_eq]
  have hz : (r : ℂ) * (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
    simpa only [intervalIntegral.integral_const_mul, hend, sub_self] using heq
  exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hr)

theorem exists_green_support_radius {φ : ℂ → ℂ} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  obtain ⟨R, hR, hs⟩ := hφ.isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hn : z ∉ tsupport φ := by
    intro hmem
    have hlt : ‖z‖ < R := by simpa using hs hmem
    exact not_lt_of_ge hz hlt
  exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn⟩

private theorem integrableOn_polarRectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi)) :
    MeasureTheory.IntegrableOn G (Set.Ioc 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  apply
    (hG.integrableOn_compact
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)).mono_set
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  exact ⟨⟨hr.1.le, hr.2⟩, ⟨hθ.1.le, hθ.2.le⟩⟩

theorem integrableOn_polarTarget_of_radial_support {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) : MeasureTheory.IntegrableOn G polarCoord.target := by
  apply
    (integrableOn_polarRectangle hG).of_forall_sdiff_eq_zero
      polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ ⟨hp, hnot⟩
  apply hzero
  by_contra hr
  exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

theorem integral_polarTarget_eq_rectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ p in Set.Ioc 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p := by
  apply
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      polarCoord.open_target.measurableSet
  · rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  · rintro ⟨r, θ⟩ ⟨hp, hnot⟩
    apply hzero
    by_contra hr
    exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

theorem integral_polarTarget_eq_radius_angle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ r in 0..R, ∫ θ in (-Real.pi)..Real.pi, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod G
      (by
        simpa only [MeasureTheory.Measure.volume_eq_prod] using
          integrableOn_polarRectangle hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem integral_polarTarget_eq_angle_radius {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ θ in (-Real.pi)..Real.pi, ∫ r in 0..R, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero, MeasureTheory.Measure.volume_eq_prod, ←
    MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.integral_prod_symm G
      (by
        simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict,
          ← MeasureTheory.Measure.volume_eq_prod] using
          integrableOn_polarRectangle hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem green_polar_integrand (φ : ℂ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p)) =
      (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
  have hr : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [polarCoord_symm_eq_greenUnit, Complex.real_smul, dbar]
  unfold greenRadial greenAngular
  rw [polar_realLinear_identity, Complex.star_def, ← Complex.inv_eq_conj (norm_greenUnit p.2)]
  field_simp

private theorem greenRadial_radius_vanish {φ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenRadial φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenRadial, hz _ hn, zero_apply]

private theorem greenAngular_radius_vanish {φ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenAngular φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenAngular, hz _ hn, zero_apply]

theorem integrableOn_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : MeasureTheory.IntegrableOn (greenRadial φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact
    integrableOn_polarTarget_of_radial_support (continuous_greenRadial hφ).continuousOn
      (greenRadial_radius_vanish hR (fun z h ↦ (hz z h).2))

theorem integrableOn_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : MeasureTheory.IntegrableOn (greenAngular φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact
    integrableOn_polarTarget_of_radial_support (continuous_greenAngular hφ).continuousOn
      (greenAngular_radius_vanish hR (fun z h ↦ (hz z h).2))

theorem integral_greenRadial_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ p in polarCoord.target, greenRadial φ p) = -(2 * (Real.pi : ℂ)) * φ 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_angle_radius hR.le (continuous_greenRadial hφ).continuousOn
      (greenRadial_radius_vanish hR (fun z h ↦ (hz z h).2))]
  have hend (θ : ℝ) : φ ((R : ℂ) * greenUnit θ) = 0 := by
    apply (hz _ _).1
    simp [abs_of_pos hR]
  simp_rw [integral_greenRadial hφ, hend, zero_sub]
  simp only [intervalIntegral.integral_const, Complex.real_smul, sub_neg_eq_add,
    Complex.ofReal_add]
  ring

theorem integral_greenAngular_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : (∫ p in polarCoord.target, greenAngular φ p) = 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_radius_angle hR.le (continuous_greenAngular hφ).continuousOn
      (greenAngular_radius_vanish hR (fun z h ↦ (hz z h).2))]
  apply intervalIntegral.integral_zero_ae
  filter_upwards with r hr
  have hr' : r ∈ Set.Ioc 0 R := by simpa only [Set.uIoc_of_le hR.le] using hr
  exact integral_greenAngular hφ hr'.1.ne'

theorem integral_inv_mul_dbar {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : (∫ w : ℂ, w⁻¹ * dbar φ w) = -(Real.pi : ℂ) * φ 0 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    (∫ p in polarCoord.target,
          p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p))) =
        ∫ p in polarCoord.target, (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
      apply MeasureTheory.setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      exact green_polar_integrand φ p hp.1
    _ =
        ((∫ p in polarCoord.target, greenRadial φ p) +
            Complex.I * (∫ p in polarCoord.target, greenAngular φ p)) /
          2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add (integrableOn_greenRadial hφ hc)
          ((integrableOn_greenAngular hφ hc).const_mul Complex.I),
        MeasureTheory.integral_const_mul]
    _ = -(Real.pi : ℂ) * φ 0 := by
      rw [integral_greenRadial_polarTarget hφ hc, integral_greenAngular_polarTarget hφ hc]
      ring

theorem cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : cauchyGreen (dbar f) z = f z := by
  let φ : ℂ → ℂ := fun w ↦ f (z - w)
  have hφ : ContDiff ℝ 1 φ := hf.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hcf.comp_homeomorph (Homeomorph.subLeft z)
  have hd : dbar φ = fun w ↦ -dbar f (z - w) := by
    funext w
    exact dbar_comp_const_sub z w ((hf.differentiable one_ne_zero) (z - w))
  have he := integral_inv_mul_dbar hφ hcφ
  have he' : -(∫ w : ℂ, w⁻¹ * dbar f (z - w)) = -((Real.pi : ℂ) * f z) := by
    simpa only [hd, mul_neg, MeasureTheory.integral_neg, φ, sub_zero, neg_mul] using he
  have hi := neg_injective he'
  unfold cauchyGreen
  rw [hi, one_div, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

theorem dbar_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : dbar (cauchyGreen f) z = f z := by
  rw [dbar_cauchyGreen_eq_cauchyGreen_dbar hf hcf, cauchyGreen_dbar hf hcf]

theorem cauchyGreen_smooth_dbar_solution {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (cauchyGreen f) ∧ ∀ z, dbar (cauchyGreen f) z = f z := by
  refine ⟨contDiff_cauchyGreen hf hcf, ?_⟩
  exact dbar_cauchyGreen (hf.of_le (by simp)) hcf


end SphereSixComplex.Analysis.CauchyGreen

