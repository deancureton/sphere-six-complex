module

public import SphereSixComplex.Periods.Uniformization.NormalizedModularJGlobalLift
import all SphereSixComplex.Periods.Uniformization.NormalizedModularJGlobalLift

@[expose] public section

/-!
# Constant deck comparison for global modular lifts

Two global holomorphic solutions of the same exact normalized modular equation differ by one
constant modular deck transformation.  The proof compares them on a small tangent ball of
ordinary values and then uses the identity theorem on the upper half-plane.
-/

noncomputable section

namespace SphereSixComplex.Periods.GlobalModularDeckComparison

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped Manifold
open SphereSixComplex.TriangleGroup
open TauCeti
open SolutionGermDeckTransitivity
open PuncturedRegularComparison

/-- The ambient-complex representative of a holomorphic upper-half-plane map is analytic on the
upper-half-plane open set. -/
theorem coe_comp_ofComplex_analyticOnNhd {τ : UpperHalfPlane → UpperHalfPlane}
    (hτ : MDiff τ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ (τ (UpperHalfPlane.ofComplex w) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro w hw
  have hcomplex : MDiff (fun z : UpperHalfPlane ↦ (τ z : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp hτ
  exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcomplex hw

/-- Any two global holomorphic lifts of the same exact source coordinate differ by a single
modular deck transformation on the whole upper half-plane. -/
theorem exists_global_modularDeck_eq
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate)
    {τ₁ τ₂ : UpperHalfPlane → UpperHalfPlane}
    (hτ₁ : MDiff τ₁) (hτ₂ : MDiff τ₂)
    (hEq₁ : ∀ z, normalizedModularJCoordinate (τ₁ z) = C.coordinate z)
    (hEq₂ : ∀ z, normalizedModularJCoordinate (τ₂ z) = C.coordinate z) :
    ∃ g : Delta, ∀ z, modularDeckHomeomorph g (τ₁ z) = τ₂ z := by
  let z : ℂ := (fuchsianOneFixedPoint : ℂ)
  let T₁ : ℂ → UpperHalfPlane := fun w ↦ τ₁ (UpperHalfPlane.ofComplex w)
  let T₂ : ℂ → UpperHalfPlane := fun w ↦ τ₂ (UpperHalfPlane.ofComplex w)
  let F : ℂ → ℂ := C.coordinate ∘ UpperHalfPlane.ofComplex
  have hz : z ∈ UpperHalfPlane.upperHalfPlaneSet := fuchsianOneFixedPoint.im_pos
  have hT₁an : AnalyticOnNhd ℂ (fun w ↦ (T₁ w : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := coe_comp_ofComplex_analyticOnNhd hτ₁
  have hT₂an : AnalyticOnNhd ℂ (fun w ↦ (T₂ w : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := coe_comp_ofComplex_analyticOnNhd hτ₂
  have hregular : ∀ᶠ w in 𝓝[≠] z, F w ∈ modularRegularValueSet :=
    sourceCoordinate_eventually_regular C hz
  have hupper : ∀ᶠ w in 𝓝[≠] z, w ∈ UpperHalfPlane.upperHalfPlaneSet :=
    (show ∀ᶠ w in nhds z, w ∈ UpperHalfPlane.upperHalfPlaneSet from
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz).filter_mono nhdsWithin_le_nhds
  let good : Set ℂ := {w | w ∈ UpperHalfPlane.upperHalfPlaneSet ∧
    F w ∈ modularRegularValueSet}
  have hgood : good ∈ 𝓝[≠] z := by
    filter_upwards [hupper, hregular] with w hwU hwreg
    exact ⟨hwU, hwreg⟩
  obtain ⟨V, hVpre, hVgood, hVfreq⟩ :=
    exists_preconnected_frequently_subset_of_mem_nhdsNE hgood
  have hVnonempty : V.Nonempty := by
    by_contra hVempty
    rw [not_nonempty_iff_eq_empty.mp hVempty] at hVfreq
    simpa using hVfreq
  obtain ⟨w₀, hw₀⟩ := hVnonempty
  have hT₁cont : ContinuousOn T₁ V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcbase := continuousOn_iff_continuous_domRestrict.mp
      ((hT₁an.mono fun w hw ↦ (hVgood hw).1).continuousOn)
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    have heq : UpperHalfPlane.coe ∘ V.domRestrict T₁ =
        V.domRestrict (fun w ↦ (T₁ w : ℂ)) := by
      funext w
      rfl
    rw [heq]
    exact hcbase
  have hT₂cont : ContinuousOn T₂ V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcbase := continuousOn_iff_continuous_domRestrict.mp
      ((hT₂an.mono fun w hw ↦ (hVgood hw).1).continuousOn)
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    have heq : UpperHalfPlane.coe ∘ V.domRestrict T₂ =
        V.domRestrict (fun w ↦ (T₂ w : ℂ)) := by
      funext w
      rfl
    rw [heq]
    exact hcbase
  have hT₁reg : ∀ w ∈ V,
      normalizedModularJCoordinate (T₁ w) ∈ modularRegularValueSet := by
    intro w hw
    rw [hEq₁]
    exact (hVgood hw).2
  have hT₂reg : ∀ w ∈ V,
      normalizedModularJCoordinate (T₂ w) ∈ modularRegularValueSet := by
    intro w hw
    rw [hEq₂]
    exact (hVgood hw).2
  have hbaseEq : normalizedModularJCoordinate (T₁ w₀) =
      normalizedModularJCoordinate (T₂ w₀) := by
    rw [hEq₁, hEq₂]
  obtain ⟨g, hgmatch⟩ := exists_delta_modularDeck_eq J hbaseEq
  have hlocal :
      (fun w ↦ (modularDeckHomeomorph g (T₁ w) : ℂ)) =ᶠ[𝓝 z]
        fun w ↦ (T₂ w : ℂ) := by
    apply eventuallyEq_modularDeck_of_regular_covering_lifts J g hVpre hw₀
      hT₁cont hT₂cont hT₁reg hT₂reg
    · intro w hw
      rw [hEq₁, hEq₂]
    · exact hgmatch
    · exact hVfreq
    · exact hT₁an z hz
    · exact hT₂an z hz
  have hDeckAn : AnalyticOnNhd ℂ
      (fun w ↦ (modularDeckHomeomorph g (T₁ w) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := by
    intro w hw
    exact analyticAt_modularDeck_coe g (hT₁an w hw)
  have hpre : IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hglobal := hDeckAn.eqOn_of_preconnected_of_eventuallyEq hT₂an hpre hz hlocal
  refine ⟨g, fun x ↦ ?_⟩
  apply UpperHalfPlane.coe_injective
  have hx := hglobal (x := (x : ℂ)) x.im_pos
  simpa only [T₁, T₂, UpperHalfPlane.ofComplex_apply] using hx


end SphereSixComplex.Periods.GlobalModularDeckComparison
