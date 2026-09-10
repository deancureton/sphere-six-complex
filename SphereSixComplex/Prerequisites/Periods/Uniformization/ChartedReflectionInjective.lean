module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Arc
import all TauCeti.Analysis.Complex.Conformal.Reflection.Arc
public import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
import all TauCeti.Analysis.Complex.Conformal.Reflection.Injective

@[expose] public section

/-!
# Injective Schwarz reflection in analytic-arc coordinates

`TauCeti.Analysis.Complex.Conformal.Reflection.Arc` transports the holomorphic Schwarz
reflection principle through biholomorphic charts.  The real-axis result in
`TauCeti.Analysis.Complex.Conformal.Reflection.Injective` additionally proves that the reflected
map is injective.  This file transports that extra conclusion through the same charts.

The result is deliberately local.  In the chamber application it applies along the relative
interior of every analytic side.  It must not be used at a corner where the desired continuation
is branched (in particular, at the source order-four / target order-two corner).
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.Reflection

variable {e d : OpenPartialHomeomorph ℂ ℂ} {f : ℂ → ℂ}

/-- The coordinate expression used by charted Schwarz reflection. -/
private def inCharts (e d : OpenPartialHomeomorph ℂ ℂ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  d (f (e.symm w))

private theorem mapsTo_inCharts_closedUpper
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source) :
    MapsTo (inCharts e d f) (e.target ∩ {w : ℂ | 0 ≤ w.im}) d.target := by
  rintro w ⟨hw, him⟩
  apply d.map_source
  apply hf_maps
  refine ⟨e.map_target hw, ?_⟩
  change 0 ≤ (e (e.symm w)).im
  change 0 ≤ w.im at him
  simpa only [e.right_inv hw] using him

private theorem mapsTo_schwarzReflection_inCharts
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source) :
    MapsTo (TauCeti.schwarzReflection (inCharts e d f)) e.target d.target := by
  intro w hw
  by_cases him : 0 ≤ w.im
  · rw [TauCeti.schwarzReflection_of_im_nonneg him]
    exact mapsTo_inCharts_closedUpper hf_maps ⟨hw, him⟩
  · have him_neg : w.im < 0 := lt_of_not_ge him
    rw [TauCeti.schwarzReflection_of_im_neg him_neg]
    apply hd_symm
    apply mapsTo_inCharts_closedUpper hf_maps
    refine ⟨he_symm hw, ?_⟩
    rw [Set.mem_ofPred_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
    exact neg_nonneg.mpr him_neg.le

private theorem mapsTo_inCharts_openUpper
    (hf_upper : MapsTo (fun z => d (f z))
      (e.source ∩ {z : ℂ | 0 < (e z).im}) {w : ℂ | 0 < w.im}) :
    MapsTo (inCharts e d f) (e.target ∩ {w : ℂ | 0 < w.im}) {w : ℂ | 0 < w.im} := by
  rintro w ⟨hw, him⟩
  apply hf_upper
  refine ⟨e.map_target hw, ?_⟩
  change 0 < (e (e.symm w)).im
  change 0 < w.im at him
  simpa only [e.right_inv hw] using him

private theorem inCharts_im_nonneg_on_axis
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0) :
    ∀ w ∈ e.target, w.im = 0 → 0 ≤ (inCharts e d f w).im := by
  intro w hw him
  have h := hf_real (e.symm w) (e.map_target hw) (by
    simpa only [e.right_inv hw] using him)
  exact h.ge

private theorem injOn_inCharts_closedUpper
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    InjOn (inCharts e d f) (e.target ∩ {w : ℂ | 0 ≤ w.im}) := by
  intro w hw v hv heq
  rcases hw with ⟨hw_target, hw_im⟩
  rcases hv with ⟨hv_target, hv_im⟩
  change 0 ≤ w.im at hw_im
  change 0 ≤ v.im at hv_im
  have hw' : e.symm w ∈ e.source ∩ {z : ℂ | 0 ≤ (e z).im} := by
    refine ⟨e.map_target hw_target, ?_⟩
    change 0 ≤ (e (e.symm w)).im
    simpa only [e.right_inv hw_target] using hw_im
  have hv' : e.symm v ∈ e.source ∩ {z : ℂ | 0 ≤ (e z).im} := by
    refine ⟨e.map_target hv_target, ?_⟩
    change 0 ≤ (e (e.symm v)).im
    simpa only [e.right_inv hv_target] using hv_im
  have hfv : f (e.symm w) = f (e.symm v) :=
    d.injOn (hf_maps hw') (hf_maps hv') heq
  exact e.symm.injOn hw_target hv_target (hf_inj hw' hv' hfv)

/-- **Injective Schwarz reflection across an analytic arc.**

The charts `e` and `d` straighten the source and target arcs.  Besides the hypotheses of Tau
Ceti's charted holomorphic reflection theorem, assume that the original branch is injective on
the closed positive side and maps the open positive side to the open upper half-plane in target
coordinates.  Then its explicit charted reflection is injective on the whole source chart.
-/
theorem injOn_chartedSchwarzReflection_of_symmetric
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hf_upper : MapsTo (fun z => d (f z))
      (e.source ∩ {z : ℂ | 0 < (e z).im}) {w : ℂ | 0 < w.im})
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    InjOn (TauCeti.chartedSchwarzReflection e d f) e.source := by
  let g := inCharts e d f
  have hg_inj : InjOn (TauCeti.schwarzReflection g) e.target :=
    TauCeti.injOn_schwarzReflection_of_symmetric he_symm
      (mapsTo_inCharts_openUpper hf_upper)
      (inCharts_im_nonneg_on_axis hf_real)
      (injOn_inCharts_closedUpper hf_maps hf_inj)
  intro z hz w hw heq
  have hzmid : TauCeti.schwarzReflection g (e z) ∈ d.target := by
    exact mapsTo_schwarzReflection_inCharts he_symm hd_symm hf_maps (e.map_source hz)
  have hwmid : TauCeti.schwarzReflection g (e w) ∈ d.target := by
    exact mapsTo_schwarzReflection_inCharts he_symm hd_symm hf_maps (e.map_source hw)
  have hmid : TauCeti.schwarzReflection g (e z) =
      TauCeti.schwarzReflection g (e w) := by
    apply d.symm.injOn hzmid hwmid
    change d.symm (TauCeti.schwarzReflection g (e z)) =
      d.symm (TauCeti.schwarzReflection g (e w)) at heq
    exact heq
  exact e.injOn hz hw (hg_inj (e.map_source hz) (e.map_source hw) hmid)

/-- The charted reflected map is conformal at every point of its source chart. -/
theorem conformalAt_chartedSchwarzReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hf_upper : MapsTo (fun z => d (f z))
      (e.source ∩ {z : ℂ | 0 < (e z).im}) {w : ℂ | 0 < w.im})
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    {z : ℂ} (hz : z ∈ e.source) :
    ConformalAt (TauCeti.chartedSchwarzReflection e d f) z := by
  apply TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn
    (TauCeti.differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm
      hd_symm hf_maps hf_cont hf_diff hf_real)
    e.open_source
    (injOn_chartedSchwarzReflection_of_symmetric he_symm hd_symm hf_maps hf_real
      hf_upper hf_inj)
    hz

/-- The inverse of a charted reflected conformal map is holomorphic on its image. -/
theorem differentiableOn_invFunOn_chartedSchwarzReflection_of_symmetric
    (he : DifferentiableOn ℂ e e.source) (hd : DifferentiableOn ℂ d d.source)
    (he_symm : MapsTo (starRingEnd ℂ) e.target e.target)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source)
    (hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}))
    (hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}))
    (hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0)
    (hf_upper : MapsTo (fun z => d (f z))
      (e.source ∩ {z : ℂ | 0 < (e z).im}) {w : ℂ | 0 < w.im})
    (hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im})) :
    DifferentiableOn ℂ
      (Function.invFunOn (TauCeti.chartedSchwarzReflection e d f) e.source)
      (TauCeti.chartedSchwarzReflection e d f '' e.source) := by
  apply TauCeti.DifferentiableOn.invFunOn
    (TauCeti.differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_symm
      hd_symm hf_maps hf_cont hf_diff hf_real)
    e.open_source
    (injOn_chartedSchwarzReflection_of_symmetric he_symm hd_symm hf_maps hf_real
      hf_upper hf_inj)


end SphereSixComplex.Periods.Reflection
