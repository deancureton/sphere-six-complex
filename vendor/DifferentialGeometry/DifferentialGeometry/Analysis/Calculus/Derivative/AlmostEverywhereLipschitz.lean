module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DifferentialGeometry.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {L C : ℝ≥0} {f : E → F}

theorem portPrivate_e6769324_dual_affine_increment_le_on_of_ae_fderiv
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s) (hf : LipschitzOnWith L f s)
    (p : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (hD : ∀ᵐ x ∂μ.restrict s, ‖fderiv ℝ f x - p - B x‖ ≤ C)
    (ell : F →L[ℝ] ℝ) (hell : ‖ell‖ ≤ 1) (v a : E) (ha : a ∈ s) (hav : a + v ∈ s) :
    ‖ell (f (a + v) - f a - p v - B a v - (1 / 2 : ℝ) • B v v)‖ ≤ C * ‖v‖ := by
  have hdiff : ∀ᵐ x ∂μ.restrict s, DifferentiableAt ℝ f x := by
    filter_upwards [hf.ae_differentiableWithinAt hs.measurableSet,
      ae_restrict_mem hs.measurableSet] with x hx hxs
    exact hx.differentiableAt (hs.mem_nhds hxs)
  have hgood : ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x - p - B x‖ ≤ C :=
    (ae_restrict_iff' hs.measurableSet).mp (hdiff.and hD)
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null
    (show μ {x | ¬(x ∈ s → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x - p - B x‖ ≤ C)} = 0 from hgood)
  have hNfull : ∀ᵐ x ∂μ, x ∈ Nᶜ := measure_eq_zero_iff_ae_notMem.mp hNzero
  have hNgood {x : E} (hx : x ∈ Nᶜ) :
      x ∈ s → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x - p - B x‖ ≤ C := by
    by_contra hn
    exact hx (hNsub hn)
  let line : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hlines : ∀ᵐ b ∂μ, ∀ᵐ (t : ℝ) ∂volume, b + t • v ∈ Nᶜ := by
    have hraw := (ae_ae_add_linearMap_mem_iff line.toLinearMap volume μ hNm.compl).2 hNfull
    change ∀ᵐ b ∂μ, ∀ᵐ (t : ℝ) ∂volume, b + line t ∈ Nᶜ at hraw
    exact hraw
  let T : Set E := {b | b ∈ s ∧ b + v ∈ s}
  have hT : IsOpen T := hs.inter (hs.preimage (continuous_id.add continuous_const))
  have haT : a ∈ T := ⟨ha, hav⟩
  have hbound : ∀ᵐ b ∂μ, b ∈ T → ‖ell (f (b + v) - f b - p v - B b v - (1 / 2 : ℝ) • B v v)‖ ≤ C * ‖v‖ := by
    filter_upwards [hlines] with b hb
    intro hbT
    have hseg : MapsTo (fun t : ℝ => b + t • v) (uIcc 0 1) s := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      simpa only [add_sub_cancel_left] using hconv.add_smul_sub_mem hbT.1 hbT.2 ht'
    let u : ℝ → ℝ := fun t => ell (f (b + t • v))
    have hlineLip : LipschitzWith (0 + ‖line‖₊) (fun t : ℝ => b + t • v) := by
      exact (LipschitzWith.const b).add line.lipschitzWith
    have huLip : LipschitzOnWith (‖ell‖₊ * (L * (0 + ‖line‖₊))) u (uIcc 0 1) :=
      ell.lipschitzWith.comp_lipschitzOnWith (hf.comp hlineLip.lipschitzOnWith hseg)
    have huAC : AbsolutelyContinuousOnInterval u 0 1 := huLip.absolutelyContinuousOnInterval
    let w : ℝ → ℝ := fun t => u t - t * ell (p v + B b v) - t ^ 2 / 2 * ell (B v v)
    have hpoly₁ : ContDiff ℝ 1 (fun t : ℝ => t * ell (p v + B b v)) := by fun_prop
    have hpoly₂ : ContDiff ℝ 1 (fun t : ℝ => t ^ 2 / 2 * ell (B v v)) := by fun_prop
    have hwAC : AbsolutelyContinuousOnInterval w 0 1 :=
      (huAC.sub hpoly₁.contDiffOn.absolutelyContinuousOnInterval).sub
        hpoly₂.contDiffOn.absolutelyContinuousOnInterval
    have huD : ∀ᵐ (t : ℝ) ∂volume, t ∈ uIcc 0 1 → ‖deriv w t‖ ≤ C * ‖v‖ := by
      filter_upwards [hb] with t ht
      intro hts
      have hx := hNgood ht (hseg hts)
      have hcurve : HasDerivAt (fun z : ℝ => b + z • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add b
      have hud : HasDerivAt u (ell (fderiv ℝ f (b + t • v) v)) t :=
        ell.hasFDerivAt.comp_hasDerivAt t (hx.1.hasFDerivAt.comp_hasDerivAt t hcurve)
      have hw₁ := (hasDerivAt_id t).mul_const (ell (p v + B b v))
      have hw₂ := (((hasDerivAt_id t).pow 2).div_const 2).mul_const (ell (B v v))
      have hwd : HasDerivAt w (ell ((fderiv ℝ f (b + t • v) - p - B (b + t • v)) v)) t := by
        apply ((hud.sub hw₁).sub hw₂).congr_deriv
        simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply, smul_eq_mul, id_eq]
        ring
      rw [hwd.deriv]
      calc
        ‖ell ((fderiv ℝ f (b + t • v) - p - B (b + t • v)) v)‖ ≤ ‖ell‖ * ‖(fderiv ℝ f (b + t • v) - p - B (b + t • v)) v‖ :=
          ell.le_opNorm _
        _ ≤ 1 * (C * ‖v‖) :=
          mul_le_mul hell ((fderiv ℝ f (b + t • v) - p - B (b + t • v)).le_opNorm v |>.trans
            (mul_le_mul_of_nonneg_right hx.2 (norm_nonneg v))) (norm_nonneg _) zero_le_one
        _ = C * ‖v‖ := one_mul _
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := (0 : ℝ)) (b := 1) (huD.mono fun t ht hts => ht (uIoc_subset_uIcc hts))
    rw [hwAC.integral_deriv_eq_sub] at hi
    convert hi using 1
    · simp only [w, u, one_smul, zero_smul, add_zero, map_sub, map_add, map_smul,
        smul_eq_mul, sub_zero, one_mul, zero_mul, one_pow, one_div]
      congr 1
      ring
    · simp
  have hleft : ContinuousAt (fun b : E => f (b + v)) a :=
    ContinuousAt.comp (f := fun b : E => b + v) (x := a)
      ((hf.continuousOn (a + v) hav).continuousAt (hs.mem_nhds hav))
      (continuous_id.add continuous_const).continuousAt
  have hright : ContinuousAt f a :=
    (hf.continuousOn a ha).continuousAt (hs.mem_nhds ha)
  have hc : ContinuousAt (fun b : E => ‖ell (f (b + v) - f b - p v - B b v - (1 / 2 : ℝ) • B v v)‖) a :=
    (ell.continuous.continuousAt.comp
      ((((hleft.sub hright).sub continuousAt_const).sub
        ((B.continuous.clm_apply continuous_const).continuousAt)).sub continuousAt_const)).norm
  have hacl : a ∈ closure {b : E | ‖ell (f (b + v) - f b - p v - B b v - (1 / 2 : ℝ) • B v v)‖ ≤ C * ‖v‖} := by
    rw [_root_.mem_closure_iff]
    intro O hO haO
    obtain ⟨b, hbOT, hb⟩ := _root_.mem_closure_iff.mp (μ.dense_of_ae hbound a)
      (O ∩ T) (hO.inter hT) ⟨haO, haT⟩
    exact ⟨b, hbOT.1, hb hbOT.2⟩
  exact hc.continuousWithinAt.closure_le hacl continuous_const.continuousWithinAt (fun _ h => h)

theorem norm_sub_quadratic_le_of_ae_norm_fderiv_sub_le
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s) (hf : LipschitzOnWith L f s)
    (p : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (hD : ∀ᵐ x ∂μ.restrict s, ‖fderiv ℝ f x - p - B x‖ ≤ C)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    ‖f b - f a - p (b - a) - B a (b - a) - (1 / 2 : ℝ) • B (b - a) (b - a)‖ ≤
      C * ‖b - a‖ := by
  obtain ⟨ell, hell, hattain⟩ := exists_dual_vector'' ℝ
    (f b - f a - p (b - a) - B a (b - a) - (1 / 2 : ℝ) • B (b - a) (b - a))
  have h := portPrivate_e6769324_dual_affine_increment_le_on_of_ae_fderiv hs hconv hf p B hD ell hell (b - a) a ha
    (by simpa only [add_sub_cancel] using hb)
  rw [add_sub_cancel, hattain] at h
  simpa only [norm_algebraMap', norm_norm] using h


theorem lipschitzOnWith_of_ae_norm_fderiv_le
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s) (hf : LipschitzOnWith L f s)
    (hD : ∀ᵐ x ∂μ.restrict s, ‖fderiv ℝ f x‖ ≤ C) : LipschitzOnWith C f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := norm_sub_quadratic_le_of_ae_norm_fderiv_sub_le hs hconv hf 0 0
    (by simpa only [sub_zero, zero_apply] using hD) hx hy
  simpa only [zero_apply, smul_zero, sub_zero, dist_eq_norm, norm_sub_rev] using h

theorem lipschitzWith_of_ae_norm_fderiv_le
    (hf : LipschitzWith L f) (hD : ∀ᵐ x ∂μ, ‖fderiv ℝ f x‖ ≤ C) :
    LipschitzWith C f := by
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_ae_norm_fderiv_le isOpen_univ convex_univ hf.lipschitzOnWith
    (by simpa only [Measure.restrict_univ] using hD)

end DifferentialGeometry.Analysis
