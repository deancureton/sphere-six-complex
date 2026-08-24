module

public import SphereSixComplex.Periods.FuchsianCuspNormalization
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Exact completed-cusp germ of the lifted modular frame

This module turns a holomorphic, parabolic-invariant square root of the pulled-back weight-six
Eisenstein series into the completed-cusp data for the modular frame
`E₄² * sqrt(E₆) / Δ`.  The construction is local at the cusp: its factorization is deliberately
stated eventually in `upperHalfPlaneAtInfinity`.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open Filter Set Metric
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.FuchsianCuspNormalization

private theorem sourceCuspQ_tendsto_zero :
    Tendsto fuchsianSourceCuspQ upperHalfPlaneAtInfinity (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrange : Set.range UpperHalfPlane.im ∈ (atTop : Filter ℝ) := by
    apply eventually_atTop.2
    refine ⟨1, fun y hy => ?_⟩
    refine ⟨⟨⟨0, y⟩, by linarith⟩, rfl⟩
  change Tendsto
    ((fun z : UpperHalfPlane => ‖Function.Periodic.qParam sourceCuspWidth (z : ℂ)‖))
    (comap UpperHalfPlane.im atTop) (nhds 0)
  simp_rw [Function.Periodic.norm_qParam]
  apply (tendsto_comap'_iff (m := fun y : ℝ =>
    Real.exp (-2 * Real.pi * y / sourceCuspWidth)) hrange).2
  exact Real.tendsto_exp_atBot.comp
    (.atBot_div_const sourceCuspWidth_pos
      (tendsto_id.const_mul_atTop_of_neg (by simpa using Real.pi_pos)))

private theorem inverseCoordinate_tendsto_zero
    (C : ExactFuchsianOrbifoldCoordinate) :
    Tendsto (fun z => (C.coordinate z)⁻¹) upperHalfPlaneAtInfinity (nhds 0) := by
  have hq := sourceCuspQ_tendsto_zero
  have hzero_mem : (0 : ℂ) ∈ Metric.ball 0 C.cusp.cuspRadius := by
    simpa using C.cusp.cuspRadius_pos
  have hunit : Tendsto (fun z => C.cusp.cuspUnit (fuchsianSourceCuspQ z))
      upperHalfPlaneAtInfinity (nhds (C.cusp.cuspUnit 0)) :=
    (C.cusp.cuspUnit_holomorphic 0 hzero_mem).continuousAt.tendsto.comp hq
  have hproduct : Tendsto
      (fun z => fuchsianSourceCuspQ z * C.cusp.cuspUnit (fuchsianSourceCuspQ z))
      upperHalfPlaneAtInfinity (nhds 0) := by
    simpa using hq.mul hunit
  apply hproduct.congr'
  filter_upwards [C.cusp.reciprocal_factorization] with z hz
  exact hz.symm

private theorem periodic_of_parabolic_invariant
    (s : UpperHalfPlane → ℂ)
    (hs : ∀ z, s (fuchsianSourceAction g₀ • z) = s z) :
    Function.Periodic (s ∘ UpperHalfPlane.ofComplex) (sourceCuspWidth : ℂ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + sourceCuspWidth).im := by simpa using hz
    let w : UpperHalfPlane := ⟨z + sourceCuspWidth, hz'⟩
    have hw : fuchsianSourceAction g₀ • w = ⟨z, hz⟩ := by
      apply UpperHalfPlane.coe_injective
      change (((fuchsianSourceAction g₀) w : UpperHalfPlane) : ℂ) = z
      rw [sourceCusp_translation]
      simp [w]
    change s (UpperHalfPlane.ofComplex (z + sourceCuspWidth)) =
      s (UpperHalfPlane.ofComplex z)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz',
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    change s w = s ⟨z, hz⟩
    rw [← hw, hs]
  · have hz' : ¬ 0 < (z + sourceCuspWidth).im := by simpa using hz
    exact congrArg s (UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos
      (not_lt.mp hz') (not_lt.mp hz))

private theorem eisensteinFour_cusp_zero :
    UpperHalfPlane.cuspFunction 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by omega) ⟨2, rfl⟩
  simpa [UpperHalfPlane.qExpansion_coeff] using h

private theorem eisensteinSix_cusp_zero :
    UpperHalfPlane.cuspFunction 1 (ModularForm.E₆ : UpperHalfPlane → ℂ) 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by omega) ⟨3, rfl⟩
  simpa [UpperHalfPlane.qExpansion_coeff] using h

private theorem eisensteinFour_cusp_analytic :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1
      (ModularForm.E₄ : UpperHalfPlane → ℂ)) 0 := by
  exact ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos
    one_mem_strictPeriods_SL

private theorem eisensteinSix_cusp_analytic :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1
      (ModularForm.E₆ : UpperHalfPlane → ℂ)) 0 := by
  exact ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ one_pos
    one_mem_strictPeriods_SL

/-- Completed-cusp data for the modular frame attached to a chosen square root of the pulled-back
weight-six Eisenstein series.

The reciprocal source quotient coordinate and the frame are related only sufficiently far into
the cusp.  This is the precise germ statement compatible with the non-parabolic elliptic
automorphy of the frame. -/
public structure ExactFuchsianCuspFrameGerm
    (E : EstablishedFuchsianModularParameter) (s : UpperHalfPlane → ℂ) where
  /-- The holomorphic unit remaining after the simple cusp pole is removed. -/
  cuspUnit : ℂ → ℂ
  /-- Radius of a completed source-cusp coordinate neighborhood. -/
  cuspRadius : ℝ
  /-- The completed source-cusp neighborhood is nontrivial. -/
  cuspRadius_pos : 0 < cuspRadius
  /-- The cusp unit is holomorphic throughout the chosen coordinate neighborhood. -/
  cuspUnit_holomorphic : ∀ q, q ∈ Metric.ball 0 cuspRadius → MDiffAt cuspUnit q
  /-- The extending factor is a unit at the added cusp point. -/
  cuspUnit_zero_ne : cuspUnit 0 ≠ 0
  /-- Eventually the reciprocal quotient coordinate lies in a compact subdisc of the unit's
  domain. -/
  inverse_coordinate_eventually_mem_closedBall :
    ∀ᶠ z in upperHalfPlaneAtInfinity,
      (E.sourceCoordinate.coordinate z)⁻¹ ∈ Metric.closedBall 0 (cuspRadius / 2)
  /-- Exact simple-pole normalization of the modular frame as a completed-cusp germ. -/
  cusp_factorization_eventually :
    ∀ᶠ z in upperHalfPlaneAtInfinity,
      (E.sourceCoordinate.coordinate z)⁻¹ *
          (ModularForm.E₄ (E.modularParameter.tau z) ^ 2 * s z /
            ModularForm.discriminant (E.modularParameter.tau z)) =
        cuspUnit ((E.sourceCoordinate.coordinate z)⁻¹)

/-- A holomorphic parabolic-invariant square root of the pulled-back weight-six Eisenstein
series has a holomorphic germ in the completed source cusp parameter. -/
public theorem exists_sqrtEisensteinSixCuspGerm
    (E : EstablishedFuchsianModularParameter)
    (s : UpperHalfPlane → ℂ)
    (hs_holomorphic : MDiff s)
    (hs_sq : ∀ z, s z ^ 2 = ModularForm.E₆ (E.modularParameter.tau z))
    (hs_cusp : ∀ z, s (fuchsianSourceAction g₀ • z) = s z) :
    ∃ sGerm : ℂ → ℂ,
      AnalyticAt ℂ sGerm 0 ∧
      sGerm 0 ≠ 0 ∧
      ∀ z, sGerm (fuchsianSourceCuspQ z) = s z := by
  obtain ⟨phi, hphi_analytic, _hphi_order, hphi_zero, hphi_factor⟩ :=
    Established.exists_parabolicCuspSimpleGerm sourceCuspWidth 1
      sourceCuspWidth_pos zero_lt_one E.modularParameter.tau
      E.modularParameter.tau_holomorphic
      (establishedModularParameter_tau_translate E)
  let e6q : ℂ → ℂ := UpperHalfPlane.cuspFunction 1
    (ModularForm.E₆ : UpperHalfPlane → ℂ)
  have he6q_analytic : AnalyticAt ℂ e6q 0 := eisensteinSix_cusp_analytic
  have he6q_zero : e6q 0 = 1 := eisensteinSix_cusp_zero
  have htarget (z : UpperHalfPlane) :
      e6q (phi (fuchsianSourceCuspQ z)) =
        ModularForm.E₆ (E.modularParameter.tau z) := by
    rw [show fuchsianSourceCuspQ z =
        Function.Periodic.qParam sourceCuspWidth (z : ℂ) by rfl,
      hphi_factor]
    exact SlashInvariantFormClass.eq_cuspFunction
      (f := ModularForm.E₆) (E.modularParameter.tau z)
      one_mem_strictPeriods_SL one_ne_zero
  have hq := sourceCuspQ_tendsto_zero
  have htarget_tendsto : Tendsto
      (fun z => e6q (phi (fuchsianSourceCuspQ z)))
      upperHalfPlaneAtInfinity (nhds 1) := by
    have ht :=
      (he6q_analytic.comp_of_eq hphi_analytic hphi_zero).continuousAt.tendsto.comp hq
    have hval : (e6q ∘ phi) 0 = 1 := by
      simp only [Function.comp_apply, hphi_zero, he6q_zero]
    rw [hval] at ht
    exact ht.congr' (Eventually.of_forall fun _ => rfl)
  have htarget_bounded : ∀ᶠ z in upperHalfPlaneAtInfinity,
      ‖e6q (phi (fuchsianSourceCuspQ z))‖ ≤ 2 := by
    have hclosed := htarget_tendsto.eventually
      (Metric.closedBall_mem_nhds (1 : ℂ) zero_lt_one)
    filter_upwards [hclosed] with z hz
    have hdist : dist (e6q (phi (fuchsianSourceCuspQ z))) 1 ≤ 1 :=
      Metric.mem_closedBall.mp hz
    rw [dist_eq_norm] at hdist
    calc
      ‖e6q (phi (fuchsianSourceCuspQ z))‖
          ≤ ‖e6q (phi (fuchsianSourceCuspQ z)) - 1‖ + ‖(1 : ℂ)‖ :=
            norm_le_norm_sub_add _ _
      _ ≤ 2 := by norm_num; linarith
  have hs_bounded : UpperHalfPlane.IsBoundedAtImInfty s := by
    rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    rw [upperHalfPlaneAtInfinity, eventually_comap, eventually_atTop] at htarget_bounded
    obtain ⟨A, hA⟩ := htarget_bounded
    refine ⟨2, A, fun z hz => ?_⟩
    have ht := hA z.im hz z rfl
    rw [htarget, ← hs_sq] at ht
    rw [norm_pow] at ht
    nlinarith [norm_nonneg (s z)]
  have hs_periodic := periodic_of_parabolic_invariant s hs_cusp
  let sGerm : ℂ → ℂ := UpperHalfPlane.cuspFunction sourceCuspWidth s
  have hsGerm_analytic : AnalyticAt ℂ sGerm 0 := by
    exact UpperHalfPlane.analyticAt_cuspFunction_zero sourceCuspWidth_pos hs_periodic
      hs_holomorphic hs_bounded
  have hsGerm_factor (z : UpperHalfPlane) :
      sGerm (fuchsianSourceCuspQ z) = s z := by
    exact UpperHalfPlane.eq_cuspFunction z sourceCuspWidth_pos.ne' hs_periodic
  have hsGerm_sq_tendsto : Tendsto (fun z => sGerm (fuchsianSourceCuspQ z) ^ 2)
      upperHalfPlaneAtInfinity (nhds (sGerm 0 ^ 2)) :=
    (hsGerm_analytic.continuousAt.tendsto.comp hq).pow 2
  have hsGerm_sq_tendsto_one : Tendsto (fun z => sGerm (fuchsianSourceCuspQ z) ^ 2)
      upperHalfPlaneAtInfinity (nhds 1) := by
    apply htarget_tendsto.congr'
    filter_upwards with z
    rw [hsGerm_factor, hs_sq, htarget]
  have hne : NeBot upperHalfPlaneAtInfinity := by
    rw [upperHalfPlaneAtInfinity]
    refine comap_neBot_iff_frequently.mpr (Eventually.frequently ?_)
    filter_upwards [eventually_gt_atTop 0] with t ht
      using ⟨⟨Complex.I * t, by simp [ht]⟩, by simp⟩
  have hsGerm_sq : sGerm 0 ^ 2 = 1 :=
    tendsto_nhds_unique' hne hsGerm_sq_tendsto hsGerm_sq_tendsto_one
  refine ⟨sGerm, hsGerm_analytic, ?_, hsGerm_factor⟩
  intro hzero
  rw [hzero, zero_pow (by omega)] at hsGerm_sq
  exact zero_ne_one hsGerm_sq

/-- The modular frame associated to a parabolic-invariant holomorphic square root has the exact
eventual simple-pole normalization required at the completed source cusp. -/
public theorem exists_exactFuchsianCuspFrameGerm
    (E : EstablishedFuchsianModularParameter)
    (s : UpperHalfPlane → ℂ)
    (hs_holomorphic : MDiff s)
    (hs_sq : ∀ z, s z ^ 2 = ModularForm.E₆ (E.modularParameter.tau z))
    (hs_cusp : ∀ z, s (fuchsianSourceAction g₀ • z) = s z) :
    Nonempty (ExactFuchsianCuspFrameGerm E s) := by
  obtain ⟨sGerm, hsGerm_analytic, hsGerm_zero_ne, hsGerm_factor⟩ :=
    exists_sqrtEisensteinSixCuspGerm E s hs_holomorphic hs_sq hs_cusp
  obtain ⟨phi, hphi_analytic, _hphi_order, hphi_zero, hphi_factor⟩ :=
    Established.exists_parabolicCuspSimpleGerm sourceCuspWidth 1
      sourceCuspWidth_pos zero_lt_one E.modularParameter.tau
      E.modularParameter.tau_holomorphic
      (establishedModularParameter_tau_translate E)
  let e4q : ℂ → ℂ := UpperHalfPlane.cuspFunction 1
    (ModularForm.E₄ : UpperHalfPlane → ℂ)
  have he4q_analytic : AnalyticAt ℂ e4q 0 := eisensteinFour_cusp_analytic
  have he4q_zero : e4q 0 = 1 := eisensteinFour_cusp_zero
  let x : ℂ → ℂ := fun q => q * E.sourceCoordinate.cusp.cuspUnit q
  have hcuspUnit_analytic :
      AnalyticAt ℂ E.sourceCoordinate.cusp.cuspUnit 0 := by
    apply DifferentiableOn.analyticAt
      (s := Metric.ball (0 : ℂ) E.sourceCoordinate.cusp.cuspRadius)
    · intro q hq
      exact (mdifferentiableAt_iff_differentiableAt.mp
        (E.sourceCoordinate.cusp.cuspUnit_holomorphic q hq)).differentiableWithinAt
    · exact Metric.ball_mem_nhds 0 E.sourceCoordinate.cusp.cuspRadius_pos
  have hx_analytic : AnalyticAt ℂ x 0 := by
    exact analyticAt_id.mul hcuspUnit_analytic
  have hx_zero : x 0 = 0 := by simp [x]
  have hx_deriv : deriv x 0 = E.sourceCoordinate.cusp.cuspUnit 0 := by
    have h := (hasDerivAt_id' (0 : ℂ)).mul
      hcuspUnit_analytic.differentiableAt.hasDerivAt
    have hder := h.deriv
    have hfun : ((fun q : ℂ => q) * E.sourceCoordinate.cusp.cuspUnit) = x := by
      funext q
      rfl
    rw [← hfun]
    simpa only [one_mul, zero_mul, add_zero] using hder
  have hx_deriv_ne : deriv x 0 ≠ 0 := hx_deriv.symm ▸
    E.sourceCoordinate.cusp.cuspUnit_zero_ne
  let hx_strict : HasStrictDerivAt x (deriv x 0) 0 := hx_analytic.hasStrictDerivAt
  let chi : ℂ → ℂ := hx_strict.localInverse x (deriv x 0) 0 hx_deriv_ne
  have hchi_analytic : AnalyticAt ℂ chi 0 := by
    simpa only [chi, hx_zero] using hx_analytic.analyticAt_localInverse hx_deriv_ne
  have hchi_zero : chi 0 = 0 := by
    simpa only [chi, hx_zero] using
      (hx_strict.hasStrictFDerivAt_equiv hx_deriv_ne).localInverse_apply_image
  let a : ℂ → ℂ := sGerm ∘ chi
  let p : ℂ → ℂ := phi ∘ chi
  let b : ℂ → ℂ := e4q ∘ p
  have ha_analytic : AnalyticAt ℂ a 0 := by
    exact hsGerm_analytic.comp_of_eq hchi_analytic hchi_zero
  have hp_analytic : AnalyticAt ℂ p 0 := by
    exact hphi_analytic.comp_of_eq hchi_analytic hchi_zero
  have hp_zero : p 0 = 0 := by simp [p, hchi_zero, hphi_zero]
  have hb_analytic : AnalyticAt ℂ b 0 := by
    exact he4q_analytic.comp_of_eq hp_analytic hp_zero
  have hb_zero : b 0 = 1 := by simp [b, p, hchi_zero, hphi_zero, he4q_zero]
  let cuspUnit : ℂ → ℂ := fun q => 1728 * a q / b q
  have hcuspUnit_analytic : AnalyticAt ℂ cuspUnit 0 := by
    exact (analyticAt_const.mul ha_analytic).div hb_analytic (by simp [hb_zero])
  have hcuspUnit_zero_ne : cuspUnit 0 ≠ 0 := by
    change 1728 * a 0 / b 0 ≠ 0
    rw [hb_zero, div_one]
    exact mul_ne_zero (by norm_num) (by simpa [a, hchi_zero] using hsGerm_zero_ne)
  obtain ⟨cuspRadius, hcuspRadius_pos, hcuspRadius_sub⟩ :=
    Metric.mem_nhds_iff.mp hcuspUnit_analytic.eventually_analyticAt
  refine ⟨⟨cuspUnit, cuspRadius, hcuspRadius_pos, ?_, hcuspUnit_zero_ne, ?_, ?_⟩⟩
  · intro q hq
    exact mdifferentiableAt_iff_differentiableAt.mpr
      (hcuspRadius_sub hq).differentiableAt
  · exact (inverseCoordinate_tendsto_zero E.sourceCoordinate).eventually
      (Metric.closedBall_mem_nhds 0 (half_pos hcuspRadius_pos))
  · have hleft : ∀ᶠ q in nhds 0, chi (x q) = q := by
      simpa only [chi] using hx_strict.eventually_left_inverse hx_deriv_ne
    have hleft_cusp : ∀ᶠ z in upperHalfPlaneAtInfinity,
        chi (x (fuchsianSourceCuspQ z)) = fuchsianSourceCuspQ z :=
      sourceCuspQ_tendsto_zero.eventually hleft
    have he4factor (z : UpperHalfPlane) :
        e4q (phi (fuchsianSourceCuspQ z)) =
          ModularForm.E₄ (E.modularParameter.tau z) := by
      rw [show fuchsianSourceCuspQ z =
          Function.Periodic.qParam sourceCuspWidth (z : ℂ) by rfl,
        hphi_factor]
      exact SlashInvariantFormClass.eq_cuspFunction
        (f := ModularForm.E₄) (E.modularParameter.tau z)
        one_mem_strictPeriods_SL one_ne_zero
    have he4_tendsto : Tendsto
        (fun z => e4q (phi (fuchsianSourceCuspQ z)))
        upperHalfPlaneAtInfinity (nhds 1) := by
      have ht :=
        (he4q_analytic.comp_of_eq hphi_analytic hphi_zero).continuousAt.tendsto.comp
          sourceCuspQ_tendsto_zero
      have hval : (e4q ∘ phi) 0 = 1 := by
        simp only [Function.comp_apply, hphi_zero, he4q_zero]
      rw [hval] at ht
      exact ht.congr' (Eventually.of_forall fun _ => rfl)
    have he4_ne : ∀ᶠ z in upperHalfPlaneAtInfinity,
        e4q (phi (fuchsianSourceCuspQ z)) ≠ 0 :=
      he4_tendsto.eventually_ne one_ne_zero
    filter_upwards [E.sourceCoordinate.cusp.reciprocal_factorization,
      E.sourceCoordinate.cusp.coordinate_eventually_ne_zero, hleft_cusp, he4_ne]
      with z hrec hcoord hleftz he4z
    have hchi : chi (E.sourceCoordinate.coordinate z)⁻¹ =
        fuchsianSourceCuspQ z := by
      rw [hrec]
      exact hleftz
    have he4tau : ModularForm.E₄ (E.modularParameter.tau z) ≠ 0 := by
      rwa [he4factor] at he4z
    have hframe :
        (E.sourceCoordinate.coordinate z)⁻¹ *
            (ModularForm.E₄ (E.modularParameter.tau z) ^ 2 * s z /
              ModularForm.discriminant (E.modularParameter.tau z)) =
          1728 * s z / ModularForm.E₄ (E.modularParameter.tau z) := by
      have hj := E.induced_coordinate z
      change ModularForm.E₄ (E.modularParameter.tau z) ^ 3 /
          ModularForm.discriminant (E.modularParameter.tau z) / 1728 =
        E.sourceCoordinate.coordinate z at hj
      rw [← hj]
      field_simp [ModularForm.discriminant_ne_zero, he4tau]
    rw [hframe]
    change 1728 * s z / ModularForm.E₄ (E.modularParameter.tau z) =
      1728 * a ((E.sourceCoordinate.coordinate z)⁻¹) /
        b ((E.sourceCoordinate.coordinate z)⁻¹)
    rw [show a ((E.sourceCoordinate.coordinate z)⁻¹) = s z by
      simp only [a, Function.comp_apply, hchi, hsGerm_factor]]
    rw [show b ((E.sourceCoordinate.coordinate z)⁻¹) =
        ModularForm.E₄ (E.modularParameter.tau z) by
      simp only [b, p, Function.comp_apply, hchi, he4factor]]

end SphereSixComplex.Periods
