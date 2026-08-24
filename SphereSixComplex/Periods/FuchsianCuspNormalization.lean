module

public import SphereSixComplex.Geometry.CuspPeriodExpansion
import all SphereSixComplex.Periods.FuchsianUniformizationBridge
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Normalizing the Fuchsian cusp coordinate

This file isolates the general parabolic-cusp inverse theorem needed to turn the assembled
Fuchsian modular parameter into the normalized coordinate used by the cusp expansion. The exact
source and target cusp records identify the correct cusps, but their present APIs do not provide
the completed cusp map or its nonzero derivative at the added point.
-/

@[expose] public section

noncomputable section

open Filter Set Metric
open scoped Manifold Topology Real

namespace SphereSixComplex.Periods.FuchsianCuspNormalization

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup

/-- The complex half-plane above a real height. -/
public def upperHalfPlaneAbove (height : ℝ) : Set ℂ :=
  {s | height < s.im}

/-- Translation of the upper half-plane to the left by a real width. -/
public noncomputable def upperHalfPlaneRealTranslate
    (width : ℝ) (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(z : ℂ) - width, by simpa using z.im_pos⟩

@[simp]
public theorem coe_upperHalfPlaneRealTranslate (width : ℝ) (z : UpperHalfPlane) :
    ((upperHalfPlaneRealTranslate width z : UpperHalfPlane) : ℂ) = (z : ℂ) - width :=
  rfl

/-- A coherent local inverse at the parabolic cusp of a translation-equivariant holomorphic map.
The inverse can be required to land above any prescribed source height. -/
public structure ParabolicCuspLocalInverse
    (sourceWidth targetWidth sourceHeight : ℝ)
    (tau : UpperHalfPlane → UpperHalfPlane) where
  /-- Height above which the inverse is defined on the target cusp. -/
  targetHeight : ℝ
  /-- A chosen lift of the target cusp coordinate. -/
  lift : ℂ → UpperHalfPlane
  /-- The lift is holomorphic on its target half-plane. -/
  lift_holomorphic : MDiff[upperHalfPlaneAbove targetHeight] lift
  /-- The lift is a right inverse to the parabolic map. -/
  lift_tau : ∀ s ∈ upperHalfPlaneAbove targetHeight,
    ((tau (lift s) : UpperHalfPlane) : ℂ) = s
  /-- The lift lands above the requested source height. -/
  lift_source_height : ∀ s ∈ upperHalfPlaneAbove targetHeight,
    sourceHeight ≤ (lift s).im
  /-- The lift intertwines the two parabolic translations. -/
  lift_shift : ∀ s ∈ upperHalfPlaneAbove targetHeight,
    lift (s - targetWidth) = upperHalfPlaneRealTranslate sourceWidth (lift s)

namespace Established

/-- The degree-one holomorphic germ induced by a translation-equivariant half-plane map.

After passing to exponential coordinates, the equivariance makes the target cusp parameter a
holomorphic map of punctured discs. Its bounded extension has a simple zero because one source
translation maps to one target translation. -/
public theorem exists_parabolicCuspSimpleGerm
    (sourceWidth targetWidth : ℝ)
    (sourceWidth_pos : 0 < sourceWidth) (targetWidth_pos : 0 < targetWidth)
    (tau : UpperHalfPlane → UpperHalfPlane) (tau_holomorphic : MDiff tau)
    (tau_translate : ∀ z,
      tau (upperHalfPlaneRealTranslate sourceWidth z) =
        upperHalfPlaneRealTranslate targetWidth (tau z)) :
    ∃ phi : ℂ → ℂ,
      AnalyticAt ℂ phi 0 ∧
      analyticOrderAt phi 0 = 1 ∧
      phi 0 = 0 ∧
      ∀ z : UpperHalfPlane,
        phi (Function.Periodic.qParam sourceWidth (z : ℂ)) =
          Function.Periodic.qParam targetWidth ((tau z : UpperHalfPlane) : ℂ) := by
  let tauC : ℂ → ℂ := fun z ↦ ((tau (UpperHalfPlane.ofComplex z) : UpperHalfPlane) : ℂ)
  let f : UpperHalfPlane → ℂ := fun z ↦
    Function.Periodic.qParam targetWidth ((tau z : UpperHalfPlane) : ℂ)
  have htauC (z : ℂ) (hz : 0 < z.im) :
      tauC z = ((tau ⟨z, hz⟩ : UpperHalfPlane) : ℂ) := by
    simp [tauC, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have htauC_diff (z : ℂ) (hz : 0 < z.im) : DifferentiableAt ℂ tauC z := by
    change DifferentiableAt ℂ
      ((UpperHalfPlane.coe ∘ tau) ∘ UpperHalfPlane.ofComplex) z
    exact UpperHalfPlane.mdifferentiableAt_iff.mp
      ((UpperHalfPlane.mdifferentiable_coe.comp tau_holomorphic).mdifferentiableAt
        (x := ⟨z, hz⟩))
  have htau_plus (z : UpperHalfPlane) :
      tau ⟨(z : ℂ) + sourceWidth, by simpa using z.im_pos⟩ =
        ⟨((tau z : UpperHalfPlane) : ℂ) + targetWidth, by simpa using (tau z).im_pos⟩ := by
    let w : UpperHalfPlane :=
      ⟨(z : ℂ) + sourceWidth, by simpa using z.im_pos⟩
    have hw : upperHalfPlaneRealTranslate sourceWidth w = z := by
      apply UpperHalfPlane.coe_injective
      simp [w]
    have h := tau_translate w
    rw [hw] at h
    apply UpperHalfPlane.coe_injective
    have hc := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) h
    rw [coe_upperHalfPlaneRealTranslate] at hc
    rw [eq_sub_iff_add_eq] at hc
    exact hc.symm
  have hf_periodic : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (sourceWidth : ℂ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz' : 0 < (z + sourceWidth).im := by simpa using hz
      simp only [Function.comp_apply, f, UpperHalfPlane.ofComplex_apply_of_im_pos hz',
        UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      have hp := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) (htau_plus ⟨z, hz⟩)
      rw [hp]
      rw [Function.Periodic.qParam, Function.Periodic.qParam]
      rw [show 2 * (π : ℂ) * Complex.I *
          (((tau ⟨z, hz⟩ : UpperHalfPlane) : ℂ) + targetWidth) / targetWidth =
          2 * π * Complex.I * ((tau ⟨z, hz⟩ : UpperHalfPlane) : ℂ) / targetWidth +
            2 * π * Complex.I by
            field_simp [show (targetWidth : ℂ) ≠ 0 by exact_mod_cast targetWidth_pos.ne']]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    · have hz' : ¬ 0 < (z + sourceWidth).im := by simpa using hz
      simp only [Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (not_lt.mp hz') (not_lt.mp hz)]
  have hf_holomorphic : MDiff f := by
    apply (mdifferentiable_iff_differentiable.mpr
      (Function.Periodic.differentiable_qParam (h := targetWidth))).comp
    exact UpperHalfPlane.mdifferentiable_coe.comp tau_holomorphic
  have hf_bounded : UpperHalfPlane.IsBoundedAtImInfty f := by
    rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    refine ⟨1, 0, ?_⟩
    intro z _
    exact (Function.Periodic.norm_qParam_lt_one targetWidth_pos (tau z).im_pos).le
  let phi : ℂ → ℂ := UpperHalfPlane.cuspFunction sourceWidth f
  have hphi_analytic : AnalyticAt ℂ phi 0 := by
    exact UpperHalfPlane.analyticAt_cuspFunction_zero sourceWidth_pos hf_periodic
      hf_holomorphic hf_bounded
  have hphi_factor (z : ℂ) (hz : 0 < z.im) :
      phi (Function.Periodic.qParam sourceWidth z) =
        Function.Periodic.qParam targetWidth (tauC z) := by
    simpa [phi, f, tauC, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
      (UpperHalfPlane.eq_cuspFunction (f := f) ⟨z, hz⟩ sourceWidth_pos.ne' hf_periodic)
  have hphi_ne_top : analyticOrderAt phi 0 ≠ ⊤ := by
    intro htop
    have hzero := analyticOrderAt_eq_top.mp htop
    have hq_tendsto :=
      (Function.Periodic.qParam_tendsto sourceWidth_pos).mono_right nhdsWithin_le_nhds
    have hev := hq_tendsto.eventually hzero
    rw [eventually_comap] at hev
    obtain ⟨H, hH⟩ := mem_atTop_sets.mp hev
    let y : ℝ := max H 1
    let z : ℂ := y * Complex.I
    have hzim : z.im = y := by simp [z]
    have hz : phi (Function.Periodic.qParam sourceWidth z) = 0 :=
      hH y (le_max_left _ _) z hzim
    have hzpos : 0 < z.im := by rw [hzim]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    rw [hphi_factor z hzpos] at hz
    exact (Function.Periodic.qParam_ne_zero (h := targetWidth) (tauC z)) hz
  let n := analyticOrderNatAt phi 0
  have hn_order : analyticOrderAt phi 0 = (n : ℕ) := by
    exact (Nat.cast_analyticOrderNatAt hphi_ne_top).symm
  obtain ⟨g, hg_analytic, hg0, hfactor⟩ :=
    (hphi_analytic.analyticOrderAt_eq_natCast).mp hn_order
  have hg_cont : ContinuousAt g 0 := hg_analytic.continuousAt
  have hratio : Tendsto (fun q ↦ g q / g 0) (nhds 0) (nhds 1) := by
    simpa [hg0] using hg_cont.tendsto.div_const (g 0)
  have hratio_event : ∀ᶠ q in nhds 0, (fun q ↦ g q / g 0) q ∈ Complex.slitPlane := by
    apply hratio.eventually
    exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hfactor_event := hfactor
  have hq_factor : ∀ᶠ z in comap Complex.im atTop,
      phi (Function.Periodic.qParam sourceWidth z) =
        Function.Periodic.qParam sourceWidth z ^ n * g (Function.Periodic.qParam sourceWidth z) := by
    simpa [sub_zero, smul_eq_mul] using
      (Function.Periodic.qParam_tendsto sourceWidth_pos).eventually
        (hfactor_event.filter_mono nhdsWithin_le_nhds)
  have hq_slit : ∀ᶠ z in comap Complex.im atTop,
      g (Function.Periodic.qParam sourceWidth z) / g 0 ∈ Complex.slitPlane := by
    exact (Function.Periodic.qParam_tendsto sourceWidth_pos).eventually
      (hratio_event.filter_mono nhdsWithin_le_nhds)
  have hq_ganalytic : ∀ᶠ z in comap Complex.im atTop,
      AnalyticAt ℂ g (Function.Periodic.qParam sourceWidth z) := by
    exact (Function.Periodic.qParam_tendsto sourceWidth_pos).eventually
      (hg_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds)
  obtain ⟨H, hH_nonneg, hH_factor, hH_slit, hH_ganalytic⟩ : ∃ H : ℝ, 0 ≤ H ∧
      (∀ z : ℂ, H < z.im →
        phi (Function.Periodic.qParam sourceWidth z) =
          Function.Periodic.qParam sourceWidth z ^ n * g (Function.Periodic.qParam sourceWidth z)) ∧
      (∀ z : ℂ, H < z.im →
        g (Function.Periodic.qParam sourceWidth z) / g 0 ∈ Complex.slitPlane) ∧
      (∀ z : ℂ, H < z.im →
        AnalyticAt ℂ g (Function.Periodic.qParam sourceWidth z)) := by
    rw [eventually_comap] at hq_factor hq_slit hq_ganalytic
    have hboth := (hq_factor.and hq_slit).and hq_ganalytic
    obtain ⟨H, hH⟩ := mem_atTop_sets.mp hboth
    refine ⟨max H 0, le_max_right _ _, ?_, ?_, ?_⟩
    · intro z hz
      exact (hH z.im (le_trans (le_max_left _ _) hz.le)).1.1 z rfl
    · intro z hz
      exact (hH z.im (le_trans (le_max_left _ _) hz.le)).1.2 z rfl
    · intro z hz
      exact (hH z.im (le_trans (le_max_left _ _) hz.le)).2 z rfl
  let A : ℂ := 2 * π * Complex.I / targetWidth
  let B : ℂ := 2 * π * Complex.I / sourceWidth
  let delta : ℂ → ℂ := fun z ↦
    A * tauC z - (n : ℂ) * B * z -
      Complex.log (g (Function.Periodic.qParam sourceWidth z) / g 0) - Complex.log (g 0)
  have hdelta_exp (z : ℂ) (hz : H < z.im) : Complex.exp (delta z) = 1 := by
    have hz0 : 0 < z.im := lt_of_le_of_lt hH_nonneg hz
    have hfz := hphi_factor z hz0
    have hfac := hH_factor z hz
    rw [hfac] at hfz
    have hslit := hH_slit z hz
    have hgq : g (Function.Periodic.qParam sourceWidth z) ≠ 0 := by
      intro hg
      apply Complex.slitPlane_ne_zero hslit
      simp [hg]
    dsimp [delta, A, B]
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub,
      Complex.exp_log (Complex.slitPlane_ne_zero hslit),
      Complex.exp_log hg0]
    simp only [Function.Periodic.qParam]
    field_simp
    have hgq' : g (Complex.exp (2 * π * Complex.I * z / sourceWidth)) ≠ 0 := by
      simpa only [Function.Periodic.qParam] using hgq
    rw [div_eq_iff hgq']
    rw [show Complex.exp (2 * π * Complex.I * tauC z / targetWidth) =
        Complex.exp (2 * π * Complex.I * z / sourceWidth) ^ n *
          g (Complex.exp (2 * π * Complex.I * z / sourceWidth)) by
          simpa only [Function.Periodic.qParam] using hfz.symm]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hdelta_cont : ContinuousOn delta (upperHalfPlaneAbove H) := by
    intro z hz
    change H < z.im at hz
    have hz0 : 0 < z.im := lt_of_le_of_lt hH_nonneg hz
    have htau_cont := (htauC_diff z hz0).continuousAt
    have hslit := hH_slit z hz
    have hinner : ContinuousAt
        (fun w ↦ g (Function.Periodic.qParam sourceWidth w) / g 0) z :=
      (((hH_ganalytic z hz).continuousAt.comp
        (Function.Periodic.differentiable_qParam (h := sourceWidth)).continuous.continuousAt).div_const
          (g 0))
    have hlog_cont : ContinuousAt
        (fun w ↦ Complex.log (g (Function.Periodic.qParam sourceWidth w) / g 0)) z :=
      hinner.clog hslit
    apply ContinuousAt.continuousWithinAt
    dsimp [delta, A, B]
    fun_prop
  have hdelta_mem : MapsTo delta (upperHalfPlaneAbove H)
      (AddSubgroup.zmultiples (2 * π * Complex.I) : Set ℂ) := by
    intro z hz
    change H < z.im at hz
    change delta z ∈ AddSubgroup.zmultiples (2 * π * Complex.I)
    rw [AddSubgroup.mem_zmultiples_iff]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (hdelta_exp z hz)
    exact ⟨k, by simpa [zsmul_eq_mul] using hk.symm⟩
  have hdisc : IsDiscrete
      (AddSubgroup.zmultiples (2 * π * Complex.I) : Set ℂ) := by
    rw [SetLike.isDiscrete_iff_discreteTopology]
    infer_instance
  have hpre : IsPreconnected (upperHalfPlaneAbove H) := by
    exact (convex_halfSpace_im_gt H).isPreconnected
  let z0 : ℂ := (H + 1) * Complex.I
  have hz0 : z0 ∈ upperHalfPlaneAbove H := by
    change H < z0.im
    norm_num [z0, Complex.mul_im]
  have hz0sub : z0 - sourceWidth ∈ upperHalfPlaneAbove H := by
    change H < (z0 - sourceWidth).im
    norm_num [z0, Complex.sub_im, Complex.mul_im]
  have hconst := hpre.constant_of_mapsTo hdisc hdelta_cont hdelta_mem hz0sub hz0
  have htau_sub : tauC (z0 - sourceWidth) = tauC z0 - targetWidth := by
    have hzpos : 0 < z0.im := by
      apply lt_of_le_of_lt hH_nonneg
      change H < z0.im at hz0
      exact hz0
    have hzsubpos : 0 < (z0 - sourceWidth).im := by simpa using hzpos
    rw [htauC _ hzsubpos, htauC _ hzpos]
    have h := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) (tau_translate ⟨z0, hzpos⟩)
    simpa [upperHalfPlaneRealTranslate] using h
  have hq_same : Function.Periodic.qParam sourceWidth (z0 - sourceWidth) =
      Function.Periodic.qParam sourceWidth z0 := by
    rw [Function.Periodic.qParam, Function.Periodic.qParam]
    rw [show 2 * (π : ℂ) * Complex.I * (z0 - sourceWidth) / sourceWidth =
        2 * π * Complex.I * z0 / sourceWidth - 2 * π * Complex.I by
          field_simp [show (sourceWidth : ℂ) ≠ 0 by exact_mod_cast sourceWidth_pos.ne']]
    rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have hn : n = 1 := by
    dsimp [delta] at hconst
    rw [htau_sub, hq_same] at hconst
    dsimp [A, B] at hconst
    have hs : (sourceWidth : ℂ) ≠ 0 := by exact_mod_cast sourceWidth_pos.ne'
    have ht : (targetWidth : ℂ) ≠ 0 := by exact_mod_cast targetWidth_pos.ne'
    field_simp at hconst
    ring_nf at hconst
    have hcoeff :
        (2 * (π : ℂ) * Complex.I * targetWidth * sourceWidth) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero) ht) hs
    have heq :
        (2 * (π : ℂ) * Complex.I * targetWidth * sourceWidth) * ((n : ℂ) - 1) = 0 := by
      linear_combination hconst
    have hnC : (n : ℂ) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hcoeff)
    exact_mod_cast hnC
  have horder_one : analyticOrderAt phi 0 = 1 := by simpa [hn] using hn_order
  have hphi_zero : phi 0 = 0 := by
    exact apply_eq_zero_of_analyticOrderAt_ne_zero (by simp [horder_one])
  refine ⟨phi, hphi_analytic, horder_one, hphi_zero, ?_⟩
  intro z
  simpa [tauC, UpperHalfPlane.ofComplex_apply_of_im_pos z.im_pos] using
    hphi_factor (z : ℂ) z.im_pos

/-- Classical degree-one parabolic-cusp inverse theorem.

The simple germ above has a holomorphic local inverse at zero. A logarithmic lift, corrected by
its constant target-period ambiguity, gives the stated coherent inverse. This result is independent
of modular forms, period functions, and the six-sphere construction. -/
public theorem parabolicCuspLocalInverse
    (sourceWidth targetWidth sourceHeight : ℝ)
    (sourceWidth_pos : 0 < sourceWidth) (targetWidth_pos : 0 < targetWidth)
    (tau : UpperHalfPlane → UpperHalfPlane) (tau_holomorphic : MDiff tau)
    (tau_translate : ∀ z,
      tau (upperHalfPlaneRealTranslate sourceWidth z) =
        upperHalfPlaneRealTranslate targetWidth (tau z)) :
    Nonempty (ParabolicCuspLocalInverse sourceWidth targetWidth sourceHeight tau) := by
  obtain ⟨phi, hphi_analytic, horder_one, hphi_zero, hphi_factor_uhp⟩ :=
    exists_parabolicCuspSimpleGerm sourceWidth targetWidth sourceWidth_pos targetWidth_pos tau
      tau_holomorphic tau_translate
  let tauC : ℂ → ℂ := fun z ↦ ((tau (UpperHalfPlane.ofComplex z) : UpperHalfPlane) : ℂ)
  have hphi_factor (z : ℂ) (hz : 0 < z.im) :
      phi (Function.Periodic.qParam sourceWidth z) =
        Function.Periodic.qParam targetWidth (tauC z) := by
    simpa [tauC, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hphi_factor_uhp ⟨z, hz⟩
  have hphi_deriv : deriv phi 0 ≠ 0 := by
    have horder_data :=
      (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hphi_analytic).mp horder_one
    simpa using horder_data.2
  let hstrict : HasStrictDerivAt phi (deriv phi 0) 0 := hphi_analytic.hasStrictDerivAt
  let psi : ℂ → ℂ := hstrict.localInverse phi (deriv phi 0) 0 hphi_deriv
  have hpsi_analytic : AnalyticAt ℂ psi 0 := by
    simpa only [psi, hphi_zero] using hphi_analytic.analyticAt_localInverse hphi_deriv
  have hpsi_zero : psi 0 = 0 := by
    simpa only [psi, hphi_zero] using
      (hstrict.hasStrictFDerivAt_equiv hphi_deriv).localInverse_apply_image
  have hpsi_strict : HasStrictDerivAt psi (deriv phi 0)⁻¹ 0 := by
    simpa only [psi, hphi_zero] using hstrict.to_localInverse hphi_deriv
  have hpsi_deriv : deriv psi 0 ≠ 0 := by
    rw [hpsi_strict.hasDerivAt.deriv]
    exact inv_ne_zero hphi_deriv
  have hpsi_order : analyticOrderAt psi 0 = 1 :=
    hpsi_analytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hpsi_zero hpsi_deriv
  obtain ⟨k, hk_analytic, hk0, hpsi_factor⟩ :=
    (hpsi_analytic.analyticOrderAt_eq_natCast).mp hpsi_order
  have hright : ∀ᶠ q in nhds 0, phi (psi q) = q := by
    simpa only [hphi_zero, psi] using hstrict.eventually_right_inverse hphi_deriv
  have hratio_k : Tendsto (fun q ↦ k q / k 0) (nhds 0) (nhds 1) := by
    simpa [hk0] using hk_analytic.continuousAt.tendsto.div_const (k 0)
  have hratio_k_slit : ∀ᶠ q in nhds 0, k q / k 0 ∈ Complex.slitPlane := by
    exact hratio_k.eventually (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  let radius : ℝ := min 1 (Real.exp (-2 * π * sourceHeight / sourceWidth))
  have hradius_pos : 0 < radius := lt_min zero_lt_one (Real.exp_pos _)
  have hpsi_small : ∀ᶠ q in nhds 0, ‖psi q‖ < radius := by
    have h := hpsi_analytic.continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (psi 0) hradius_pos)
    simpa [hpsi_zero, mem_ball_zero_iff] using h
  have hk_eventually_analytic := hk_analytic.eventually_analyticAt
  have hpsi_factor' : ∀ᶠ q in nhds 0, psi q = q * k q := by
    simpa [sub_zero, smul_eq_mul] using hpsi_factor
  let qt : ℂ → ℂ := Function.Periodic.qParam targetWidth
  have hqt : Tendsto qt (comap Complex.im atTop) (nhds 0) :=
    (Function.Periodic.qParam_tendsto targetWidth_pos).mono_right nhdsWithin_le_nhds
  have hhigh : ∀ᶠ s in comap Complex.im atTop,
      phi (psi (qt s)) = qt s ∧
      psi (qt s) = qt s * k (qt s) ∧
      k (qt s) / k 0 ∈ Complex.slitPlane ∧
      AnalyticAt ℂ k (qt s) ∧
      ‖psi (qt s)‖ < radius := by
    filter_upwards [hqt.eventually hright, hqt.eventually hpsi_factor',
      hqt.eventually hratio_k_slit, hqt.eventually hk_eventually_analytic,
      hqt.eventually hpsi_small] with s h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  rw [eventually_comap] at hhigh
  obtain ⟨H0, hH0⟩ := mem_atTop_sets.mp hhigh
  let targetHeight : ℝ := max H0 0
  have htarget_nonneg : 0 ≤ targetHeight := le_max_right _ _
  have htarget (s : ℂ) (hs : targetHeight < s.im) :
      phi (psi (qt s)) = qt s ∧
      psi (qt s) = qt s * k (qt s) ∧
      k (qt s) / k 0 ∈ Complex.slitPlane ∧
      AnalyticAt ℂ k (qt s) ∧
      ‖psi (qt s)‖ < radius :=
    hH0 s.im (le_trans (le_max_left _ _) hs.le) s rfl
  let raw : ℂ → ℂ := fun s ↦
    (sourceWidth : ℂ) / targetWidth * s +
      (sourceWidth : ℂ) / (2 * π * Complex.I) *
        (Complex.log (k (qt s) / k 0) + Complex.log (k 0))
  have hq_raw (s : ℂ) (hs : targetHeight < s.im) :
      Function.Periodic.qParam sourceWidth (raw s) = psi (qt s) := by
    have hdata := htarget s hs
    have hslit := hdata.2.2.1
    dsimp [raw, qt]
    rw [Function.Periodic.qParam]
    rw [show 2 * (π : ℂ) * Complex.I *
        ((sourceWidth : ℂ) / targetWidth * s +
          (sourceWidth : ℂ) / (2 * π * Complex.I) *
            (Complex.log (k (Function.Periodic.qParam targetWidth s) / k 0) +
              Complex.log (k 0))) / sourceWidth =
        2 * π * Complex.I * s / targetWidth +
          Complex.log (k (Function.Periodic.qParam targetWidth s) / k 0) +
            Complex.log (k 0) by
          field_simp [show (sourceWidth : ℂ) ≠ 0 by exact_mod_cast sourceWidth_pos.ne',
            show (targetWidth : ℂ) ≠ 0 by exact_mod_cast targetWidth_pos.ne',
            Complex.two_pi_I_ne_zero]
          ring]
    rw [Complex.exp_add, Complex.exp_add,
      Complex.exp_log (Complex.slitPlane_ne_zero hslit), Complex.exp_log hk0]
    change qt s * (k (qt s) / k 0) * k 0 = psi (qt s)
    rw [hdata.2.1]
    field_simp
  have hraw_source (s : ℂ) (hs : targetHeight < s.im) :
      sourceHeight < (raw s).im := by
    apply (Function.Periodic.norm_qParam_lt_iff sourceWidth_pos sourceHeight (raw s)).mp
    rw [hq_raw s hs]
    exact lt_of_lt_of_le (htarget s hs).2.2.2.2 (min_le_right _ _)
  have hraw_pos (s : ℂ) (hs : targetHeight < s.im) : 0 < (raw s).im := by
    apply (Function.Periodic.norm_qParam_lt_iff sourceWidth_pos 0 (raw s)).mp
    rw [hq_raw s hs]
    simpa using lt_of_lt_of_le (htarget s hs).2.2.2.2 (min_le_left _ _)
  let rawLift : ℂ → UpperHalfPlane := fun s ↦ UpperHalfPlane.ofComplex (raw s)
  have hrawLift_coe (s : ℂ) (hs : targetHeight < s.im) :
      ((rawLift s : UpperHalfPlane) : ℂ) = raw s := by
    simp [rawLift, UpperHalfPlane.ofComplex_apply_of_im_pos (hraw_pos s hs)]
  have hraw_diff (s : ℂ) (hs : targetHeight < s.im) : DifferentiableAt ℂ raw s := by
    have hdata := htarget s hs
    have hkcomp : DifferentiableAt ℂ (fun w ↦ k (qt w)) s :=
      hdata.2.2.2.1.differentiableAt.comp s
        (Function.Periodic.differentiable_qParam (h := targetWidth)).differentiableAt
    have hinner : DifferentiableAt ℂ (fun w ↦ k (qt w) / k 0) s :=
      hkcomp.div_const _
    have hlog : DifferentiableAt ℂ (fun w ↦ Complex.log (k (qt w) / k 0)) s :=
      (hinner.hasDerivAt.clog hdata.2.2.1).differentiableAt
    dsimp [raw]
    fun_prop
  have hrawLift_mdiff : MDiff[upperHalfPlaneAbove targetHeight] rawLift := by
    intro s hs
    change targetHeight < s.im at hs
    exact ((UpperHalfPlane.mdifferentiableAt_ofComplex (hraw_pos s hs)).comp s
      (mdifferentiableAt_iff_differentiableAt.mpr (hraw_diff s hs))).mdifferentiableWithinAt
  have hq_tau_raw (s : ℂ) (hs : targetHeight < s.im) :
      Function.Periodic.qParam targetWidth
          (((tau (rawLift s) : UpperHalfPlane) : ℂ)) =
        Function.Periodic.qParam targetWidth s := by
    calc
      Function.Periodic.qParam targetWidth (((tau (rawLift s) : UpperHalfPlane) : ℂ)) =
          phi (Function.Periodic.qParam sourceWidth (raw s)) := by
            symm
            simpa [tauC, rawLift,
              UpperHalfPlane.ofComplex_apply_of_im_pos (hraw_pos s hs)] using
              hphi_factor (raw s) (hraw_pos s hs)
      _ = phi (psi (qt s)) := by rw [hq_raw s hs]
      _ = Function.Periodic.qParam targetWidth s := by
        simpa only [qt] using (htarget s hs).1
  let deltaRaw : ℂ → ℂ := fun s ↦ ((tau (rawLift s) : UpperHalfPlane) : ℂ) - s
  have hdeltaRaw_cont : ContinuousOn deltaRaw (upperHalfPlaneAbove targetHeight) := by
    intro s hs
    change targetHeight < s.im at hs
    have hraw_at : MDiffAt rawLift s :=
      (hrawLift_mdiff s hs).mdifferentiableAt
        ((isOpen_Ioi.preimage Complex.continuous_im).mem_nhds hs)
    have htau_comp : MDiffAt (tau ∘ rawLift) s :=
      tau_holomorphic.mdifferentiableAt.comp s hraw_at
    have hcoe_comp : MDiffAt (UpperHalfPlane.coe ∘ (tau ∘ rawLift)) s :=
      UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt.comp s htau_comp
    have hcont : ContinuousAt (fun w ↦ ((tau (rawLift w) : UpperHalfPlane) : ℂ)) s := by
      change ContinuousAt (UpperHalfPlane.coe ∘ (tau ∘ rawLift)) s
      exact hcoe_comp.continuousAt
    exact (hcont.sub continuousAt_id).continuousWithinAt
  have hdeltaRaw_mem : MapsTo deltaRaw (upperHalfPlaneAbove targetHeight)
      (AddSubgroup.zmultiples (targetWidth : ℂ) : Set ℂ) := by
    intro s hs
    change targetHeight < s.im at hs
    change deltaRaw s ∈ AddSubgroup.zmultiples (targetWidth : ℂ)
    rw [AddSubgroup.mem_zmultiples_iff]
    have hq := hq_tau_raw s hs
    simp only [Function.Periodic.qParam] at hq
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hq
    refine ⟨m, ?_⟩
    dsimp [deltaRaw]
    have ht : (targetWidth : ℂ) ≠ 0 := by exact_mod_cast targetWidth_pos.ne'
    field_simp [ht] at hm
    simp only [zsmul_eq_mul]
    rw [hm]
    ring
  have hdiscTarget : IsDiscrete
      (AddSubgroup.zmultiples (targetWidth : ℂ) : Set ℂ) := by
    rw [SetLike.isDiscrete_iff_discreteTopology]
    infer_instance
  have hpreTarget : IsPreconnected (upperHalfPlaneAbove targetHeight) := by
    exact (convex_halfSpace_im_gt targetHeight).isPreconnected
  let s0 : ℂ := (targetHeight + 1) * Complex.I
  have hs0 : s0 ∈ upperHalfPlaneAbove targetHeight := by
    change targetHeight < s0.im
    norm_num [s0, Complex.mul_im]
  let offset : ℂ := deltaRaw s0
  have hdeltaRaw_eq (s : ℂ) (hs : targetHeight < s.im) : deltaRaw s = offset := by
    exact hpreTarget.constant_of_mapsTo hdiscTarget hdeltaRaw_cont hdeltaRaw_mem hs hs0
  have hoffset_im : offset.im = 0 := by
    have hoffset_mem := hdeltaRaw_mem hs0
    change deltaRaw s0 ∈ AddSubgroup.zmultiples (targetWidth : ℂ) at hoffset_mem
    rw [AddSubgroup.mem_zmultiples_iff] at hoffset_mem
    obtain ⟨m, hm⟩ := hoffset_mem
    dsimp [offset]
    rw [← hm]
    simp [zsmul_eq_mul]
  have hoffset_high (s : ℂ) (hs : targetHeight < s.im) :
      targetHeight < (s - offset).im := by
    simpa [Complex.sub_im, hoffset_im] using hs
  have hqt_shift (s : ℂ) : qt (s - targetWidth) = qt s := by
    dsimp [qt]
    rw [Function.Periodic.qParam, Function.Periodic.qParam]
    rw [show 2 * (π : ℂ) * Complex.I * (s - targetWidth) / targetWidth =
        2 * π * Complex.I * s / targetWidth - 2 * π * Complex.I by
          field_simp [show (targetWidth : ℂ) ≠ 0 by exact_mod_cast targetWidth_pos.ne']]
    rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have hraw_shift (s : ℂ) : raw (s - targetWidth) = raw s - sourceWidth := by
    dsimp [raw]
    rw [hqt_shift]
    field_simp [show (targetWidth : ℂ) ≠ 0 by exact_mod_cast targetWidth_pos.ne']
    ring
  let lift : ℂ → UpperHalfPlane := fun s ↦ UpperHalfPlane.ofComplex (raw (s - offset))
  have hlift_coe (s : ℂ) (hs : targetHeight < s.im) :
      ((lift s : UpperHalfPlane) : ℂ) = raw (s - offset) := by
    simp [lift, UpperHalfPlane.ofComplex_apply_of_im_pos
      (hraw_pos (s - offset) (hoffset_high s hs))]
  have hlift_mdiff : MDiff[upperHalfPlaneAbove targetHeight] lift := by
    intro s hs
    change targetHeight < s.im at hs
    have hinner : DifferentiableAt ℂ (fun w : ℂ ↦ w - offset) s := by fun_prop
    have hcomp : DifferentiableAt ℂ (raw ∘ fun w : ℂ ↦ w - offset) s :=
      (hraw_diff (s - offset) (hoffset_high s hs)).comp s hinner
    have hshifted : DifferentiableAt ℂ (fun w : ℂ ↦ raw (w - offset)) s := by
      change DifferentiableAt ℂ (raw ∘ fun w : ℂ ↦ w - offset) s
      exact hcomp
    exact ((UpperHalfPlane.mdifferentiableAt_ofComplex
      (hraw_pos (s - offset) (hoffset_high s hs))).comp s
        (mdifferentiableAt_iff_differentiableAt.mpr hshifted)).mdifferentiableWithinAt
  refine ⟨{
    targetHeight := targetHeight
    lift := lift
    lift_holomorphic := hlift_mdiff
    lift_tau := ?_
    lift_source_height := ?_
    lift_shift := ?_
  }⟩
  · intro s hs
    change targetHeight < s.im at hs
    have hc := hdeltaRaw_eq (s - offset) (hoffset_high s hs)
    dsimp [deltaRaw, rawLift] at hc
    change ((tau (lift s) : UpperHalfPlane) : ℂ) = s
    dsimp [lift]
    linear_combination hc
  · intro s hs
    change targetHeight < s.im at hs
    change sourceHeight ≤ ((lift s : UpperHalfPlane) : ℂ).im
    rw [hlift_coe s hs]
    exact (hraw_source (s - offset) (hoffset_high s hs)).le
  · intro s hs
    change targetHeight < s.im at hs
    apply UpperHalfPlane.coe_injective
    rw [coe_upperHalfPlaneRealTranslate, hlift_coe s hs]
    have hsShift : targetHeight < (s - targetWidth).im := by simpa using hs
    rw [hlift_coe (s - targetWidth) hsShift]
    rw [show s - targetWidth - offset = (s - offset) - targetWidth by ring]
    exact hraw_shift (s - offset)

end Established

/-- Translation by the explicit source cusp width is the Fuchsian parabolic action. -/
public theorem upperHalfPlaneRealTranslate_sourceCuspWidth (z : UpperHalfPlane) :
    upperHalfPlaneRealTranslate sourceCuspWidth z = fuchsianSourceAction g₀ • z := by
  apply UpperHalfPlane.coe_injective
  change (z : ℂ) - sourceCuspWidth =
    (((fuchsianSourceAction g₀) z : UpperHalfPlane) : ℂ)
  rw [sourceCusp_translation]

/-- The established modular parameter intertwines the explicit source translation with the
unit target translation. -/
public theorem establishedModularParameter_tau_translate
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    E.modularParameter.tau (upperHalfPlaneRealTranslate sourceCuspWidth z) =
      upperHalfPlaneRealTranslate 1 (E.modularParameter.tau z) := by
  apply UpperHalfPlane.coe_injective
  rw [upperHalfPlaneRealTranslate_sourceCuspWidth, coe_upperHalfPlaneRealTranslate]
  have h := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.equivariant g₀ z)
  exact h.trans (rhoTauReal_g₀_smul (E.modularParameter.tau z))

/-- The general parabolic theorem supplies a cusp inverse for the modular parameter retained by
`EstablishedFuchsianModularParameter`. No additional source or target cusp axiom is required. -/
public theorem exists_establishedModularParameter_cuspLocalInverse
    (E : EstablishedFuchsianModularParameter) :
    Nonempty (ParabolicCuspLocalInverse sourceCuspWidth 1 1 E.modularParameter.tau) :=
  Established.parabolicCuspLocalInverse sourceCuspWidth 1 1 sourceCuspWidth_pos zero_lt_one
    E.modularParameter.tau E.modularParameter.tau_holomorphic
      (establishedModularParameter_tau_translate E)

/-- The selected assembled period family has the same exact parabolic translation law, regardless
of how its final nondegeneracy shift was selected. -/
public theorem assembledPeriodFunctions_tau_translate
    (E : EstablishedFuchsianModularParameter) (D : FuchsianPeriodLocalData E)
    (z : UpperHalfPlane) :
    (assembledFuchsianPeriodFunctions E D).tau
        (upperHalfPlaneRealTranslate sourceCuspWidth z) =
      upperHalfPlaneRealTranslate 1 ((assembledFuchsianPeriodFunctions E D).tau z) := by
  let F := assembledFuchsianPeriodFunctions E D
  apply UpperHalfPlane.coe_injective
  rw [upperHalfPlaneRealTranslate_sourceCuspWidth, coe_upperHalfPlaneRealTranslate]
  exact F.tau_transform_cusp z

/-- The general parabolic inverse theorem constructs the normalized cusp coordinate required by
the Fuchsian period expansion. -/
public theorem exists_normalizedFuchsianCuspCoordinate
    (E : EstablishedFuchsianModularParameter) (D : FuchsianPeriodLocalData E) :
    Nonempty (NormalizedFuchsianCuspCoordinate E D) := by
  let F := assembledFuchsianPeriodFunctions E D
  obtain ⟨L⟩ := Established.parabolicCuspLocalInverse sourceCuspWidth 1 1
    sourceCuspWidth_pos zero_lt_one F.tau F.tau_holomorphic
      (assembledPeriodFunctions_tau_translate E D)
  refine ⟨{
    height := L.targetHeight
    lift := L.lift
    lift_holomorphic := ?_
    lift_tau := L.lift_tau
    lift_mem_cusp := ?_
    lift_shift := ?_
  }⟩
  · simpa only [upperHalfPlaneAbove, cuspHalfPlane] using L.lift_holomorphic
  · intro s hs
    exact L.lift_source_height s hs
  · intro s hs
    have h := L.lift_shift s (by
      simpa only [upperHalfPlaneAbove, cuspHalfPlane] using hs)
    change L.lift (s - 1) = fuchsianSourceAction g₀ • L.lift s
    rw [← upperHalfPlaneRealTranslate_sourceCuspWidth]
    simpa using h

end SphereSixComplex.Periods.FuchsianCuspNormalization
