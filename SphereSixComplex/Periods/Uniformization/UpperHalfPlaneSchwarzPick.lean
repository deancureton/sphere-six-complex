module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
import all TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
public import Mathlib.Analysis.Complex.Schwarz
import all Mathlib.Analysis.Complex.Schwarz
public import SphereSixComplex.Periods.Uniformization.NormalizedModularJGlobalLift
import all SphereSixComplex.Periods.Uniformization.NormalizedModularJGlobalLift

@[expose] public section

/-!
# Schwarz--Pick on the upper half-plane

This transports the scalar unit-disc estimate in Tau Ceti along the elementary Cayley maps
centred at two arbitrary upper-half-plane points.  The pseudo-hyperbolic form is the one needed
to mark the two elliptic values of the normalized modular-J lift.
-/

noncomputable section

namespace SphereSixComplex.Periods.UpperHalfPlaneSchwarzPick

open Complex Filter Metric Set Topology
open scoped Manifold ComplexConjugate
open TauCeti

/-- The Cayley map taking `a` to zero. -/
def halfPlaneToDiscAt (a : UpperHalfPlane) (z : ℂ) : ℂ :=
  (z - (a : ℂ)) / (z - (starRingEnd ℂ) (a : ℂ))

/-- The inverse scalar fractional-linear map. -/
def discToHalfPlaneAt (a : UpperHalfPlane) (ζ : ℂ) : ℂ :=
  ((a : ℂ) - ζ * (starRingEnd ℂ) (a : ℂ)) / (1 - ζ)

theorem discToHalfPlaneAt_im (a : UpperHalfPlane) (ζ : ℂ) :
    (discToHalfPlaneAt a ζ).im =
      a.im * (1 - normSq ζ) / normSq (1 - ζ) := by
  rw [discToHalfPlaneAt, Complex.div_im]
  simp only [Complex.sub_im, Complex.mul_im, _root_.UpperHalfPlane.coe_im, Complex.conj_im,
    Complex.one_im, Complex.sub_re, Complex.mul_re, Complex.conj_re,
    _root_.UpperHalfPlane.coe_re, Complex.one_re, Complex.normSq_apply]
  ring_nf

theorem discToHalfPlaneAt_im_pos (a : UpperHalfPlane) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    0 < (discToHalfPlaneAt a ζ).im := by
  rw [discToHalfPlaneAt_im]
  have hζsq : normSq ζ < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ζ]
  have hdenne : (1 - ζ : ℂ) ≠ 0 := by
    intro h
    have : ζ = 1 := (sub_eq_zero.mp h).symm
    subst ζ
    norm_num at hζ
  exact div_pos (mul_pos a.im_pos (sub_pos.mpr hζsq))
    (Complex.normSq_pos.mpr hdenne)

theorem halfPlaneToDiscAt_norm_lt_one (a z : UpperHalfPlane) :
    ‖halfPlaneToDiscAt a (z : ℂ)‖ < 1 := by
  have hdenne : (z : ℂ) - (starRingEnd ℂ) (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    change z.im - -a.im = 0 at him
    linarith [z.im_pos, a.im_pos]
  have hsquares :
      ‖(z : ℂ) - (a : ℂ)‖ ^ 2 <
        ‖(z : ℂ) - (starRingEnd ℂ) (a : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im]
    change
      (z.re - a.re) * (z.re - a.re) + (z.im - a.im) * (z.im - a.im) <
        (z.re - a.re) * (z.re - a.re) + (z.im - -a.im) * (z.im - -a.im)
    nlinarith [z.im_pos, a.im_pos]
  have hnorm :
      ‖(z : ℂ) - (a : ℂ)‖ <
        ‖(z : ℂ) - (starRingEnd ℂ) (a : ℂ)‖ := by
    nlinarith [norm_nonneg ((z : ℂ) - (a : ℂ)),
      norm_nonneg ((z : ℂ) - (starRingEnd ℂ) (a : ℂ))]
  rw [halfPlaneToDiscAt, norm_div, div_lt_one (norm_pos_iff.mpr hdenne)]
  exact hnorm

theorem discToHalfPlaneAt_zero (a : UpperHalfPlane) :
    discToHalfPlaneAt a 0 = (a : ℂ) := by
  simp [discToHalfPlaneAt]

theorem discToHalfPlaneAt_halfPlaneToDiscAt (a z : UpperHalfPlane) :
    discToHalfPlaneAt a (halfPlaneToDiscAt a (z : ℂ)) = (z : ℂ) := by
  have hza : (z : ℂ) - (starRingEnd ℂ) (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    change z.im - -a.im = 0 at him
    linarith [z.im_pos, a.im_pos]
  have haa : (a : ℂ) - (starRingEnd ℂ) (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    change a.im - -a.im = 0 at him
    linarith [a.im_pos]
  rw [discToHalfPlaneAt, halfPlaneToDiscAt]
  field_simp [hza, haa]
  ring

private theorem coe_ofComplex_discToHalfPlaneAt (a : UpperHalfPlane) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) :
    ((UpperHalfPlane.ofComplex (discToHalfPlaneAt a ζ) : UpperHalfPlane) : ℂ) =
      discToHalfPlaneAt a ζ := by
  let q : UpperHalfPlane :=
    ⟨discToHalfPlaneAt a ζ, discToHalfPlaneAt_im_pos a hζ⟩
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (discToHalfPlaneAt_im_pos a hζ)]

private theorem discToHalfPlaneAt_analyticAt (a : UpperHalfPlane) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) : AnalyticAt ℂ (discToHalfPlaneAt a) ζ := by
  have hden : (1 - ζ : ℂ) ≠ 0 := by
    intro h
    have : ζ = 1 := (sub_eq_zero.mp h).symm
    subst ζ
    norm_num at hζ
  exact ((analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div
    (analyticAt_const.sub analyticAt_id) hden)

private theorem halfPlaneToDiscAt_analyticAt (a : UpperHalfPlane) {z : ℂ}
    (hz : 0 < z.im) : AnalyticAt ℂ (halfPlaneToDiscAt a) z := by
  have hden : z - (starRingEnd ℂ) (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    change z.im - -a.im = 0 at him
    linarith [a.im_pos]
  exact ((analyticAt_id.sub analyticAt_const).div
    (analyticAt_id.sub analyticAt_const) hden)

/-- Holomorphic maps of the upper half-plane contract the centred pseudo-hyperbolic norm. -/
theorem norm_halfPlaneToDiscAt_map_le
    (τ : UpperHalfPlane → UpperHalfPlane) (hτ : MDiff τ)
    (a b z : UpperHalfPlane) (hab : τ a = b) :
    ‖halfPlaneToDiscAt b (τ z : ℂ)‖ ≤ ‖halfPlaneToDiscAt a (z : ℂ)‖ := by
  let p : ℂ → ℂ := discToHalfPlaneAt a
  let q : ℂ → ℂ := fun w ↦ (τ (UpperHalfPlane.ofComplex w) : ℂ)
  let f : ℂ → ℂ := halfPlaneToDiscAt b ∘ q ∘ p
  have hpAnalytic : ∀ {ζ : ℂ}, ‖ζ‖ < 1 → AnalyticAt ℂ p ζ := by
    intro ζ hζ
    exact discToHalfPlaneAt_analyticAt a hζ
  have hqAnalytic : ∀ {w : ℂ}, 0 < w.im → AnalyticAt ℂ q w := by
    intro w hw
    have hcomplex : MDiff (fun u : UpperHalfPlane ↦ (τ u : ℂ)) :=
      UpperHalfPlane.mdifferentiable_coe.comp hτ
    exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcomplex hw
  have hfAnalytic : ∀ {ζ : ℂ}, ‖ζ‖ < 1 → AnalyticAt ℂ f ζ := by
    intro ζ hζ
    have hpim : 0 < (p ζ).im := discToHalfPlaneAt_im_pos a hζ
    have hqp : AnalyticAt ℂ (q ∘ p) ζ := (hqAnalytic hpim).comp (hpAnalytic hζ)
    have hqim : 0 < (q (p ζ)).im := (τ (UpperHalfPlane.ofComplex (p ζ))).im_pos
    have houterQ : AnalyticAt ℂ (halfPlaneToDiscAt b ∘ q) (p ζ) :=
      (halfPlaneToDiscAt_analyticAt b hqim).comp (hqAnalytic hpim)
    exact houterQ.comp (hpAnalytic hζ)
  have hfDiff : DifferentiableOn ℂ f (ball (0 : ℂ) 1) := by
    intro ζ hζ
    exact (hfAnalytic (by simpa [mem_ball_zero_iff] using hζ)).differentiableAt.differentiableWithinAt
  have hfMaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro ζ hζ
    have hlt : ‖ζ‖ < 1 := by simpa [mem_ball_zero_iff] using hζ
    have hval : ‖f ζ‖ < 1 := by
      simpa only [f, q, p, Function.comp_apply] using
        halfPlaneToDiscAt_norm_lt_one b (τ (UpperHalfPlane.ofComplex (p ζ)))
    simpa [mem_ball_zero_iff] using hval
  have hfzero : f 0 = 0 := by
    simp only [f, q, p, Function.comp_apply, discToHalfPlaneAt_zero]
    rw [show UpperHalfPlane.ofComplex (a : ℂ) = a by
      apply UpperHalfPlane.coe_injective
      simpa using UpperHalfPlane.ofComplex_apply a]
    rw [hab]
    simp [halfPlaneToDiscAt]
  let ξ : ℂ := halfPlaneToDiscAt a (z : ℂ)
  have hξ : ‖ξ‖ < 1 := halfPlaneToDiscAt_norm_lt_one a z
  have hbound : ‖f ξ‖ ≤ ‖ξ‖ := by
    apply Complex.norm_le_norm_of_mapsTo_ball hfDiff
      (fun u hu ↦ ball_subset_closedBall (hfMaps hu)) hfzero hξ
  have hpinv : p ξ = (z : ℂ) := discToHalfPlaneAt_halfPlaneToDiscAt a z
  have hof : UpperHalfPlane.ofComplex (p ξ) = z := by
    apply UpperHalfPlane.coe_injective
    rw [hpinv]
    simpa using UpperHalfPlane.ofComplex_apply z
  simpa only [f, q, p, ξ, Function.comp_apply, hof] using hbound


end SphereSixComplex.Periods.UpperHalfPlaneSchwarzPick
