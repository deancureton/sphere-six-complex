module

public import SphereSixComplex.Periods.Uniformization.SolutionGermCoveringContinuation
import all SphereSixComplex.Periods.Uniformization.SolutionGermCoveringContinuation
public import SphereSixComplex.Periods.FuchsianModularParameterExistence
import all SphereSixComplex.Periods.FuchsianModularParameterExistence

@[expose] public section

/-!
# Regular-locus uniqueness for modular solution germs

This file isolates the key step in fiberwise deck transitivity.  On a connected punctured
neighbourhood where both lifts avoid the modular elliptic values, exact target covering
uniqueness turns equality at one point into equality throughout that neighbourhood.  The complex
identity theorem then fills the puncture and identifies the original analytic germs.
-/

noncomputable section

namespace SphereSixComplex.Periods.SolutionGermDeckTransitivity

open Filter Matrix Metric Set Topology UpperHalfPlane
open scoped Manifold MatrixGroups
open SphereSixComplex.TriangleGroup

/-- The modular transformation prescribed by `g`, packaged as a homeomorphism of the upper
half-plane. -/
def modularDeckHomeomorph (g : Delta) : UpperHalfPlane ≃ₜ UpperHalfPlane where
  toEquiv := modularTargetAction g
  continuous_toFun := continuous_const_smul _
  continuous_invFun := by
    change Continuous ((modularTargetAction g).symm :
      UpperHalfPlane → UpperHalfPlane)
    have heq : (modularTargetAction g).symm = modularTargetAction g⁻¹ := by
      calc
        (modularTargetAction g).symm = (modularTargetAction g)⁻¹ := rfl
        _ = modularTargetAction g⁻¹ := (map_inv modularTargetAction g).symm
    rw [heq]
    change Continuous (fun z : UpperHalfPlane ↦ rhoTauReal g⁻¹ • z)
    exact continuous_const_smul _

/-- Modular deck transformations preserve the normalized modular quotient coordinate. -/
theorem normalizedModularJCoordinate_modularDeck
    (g : Delta) (τ : UpperHalfPlane) :
    normalizedModularJCoordinate (modularDeckHomeomorph g τ) =
      normalizedModularJCoordinate τ := by
  change normalizedModularJCoordinate (rhoTauReal g • τ) = _
  exact normalizedModularJCoordinate_invariant (rhoTau g) τ

/-- Exactness of a normalized modular fiber, together with surjectivity of the prescribed
triangle-group representation, supplies a deck transformation matching any two points in that
fiber. -/
theorem exists_delta_modularDeck_eq
    (J : ExactNormalizedModularJUniformization) {τ₁ τ₂ : UpperHalfPlane}
    (h : normalizedModularJCoordinate τ₁ = normalizedModularJCoordinate τ₂) :
    ∃ g : Delta, modularDeckHomeomorph g τ₁ = τ₂ := by
  obtain ⟨a, ha⟩ := (J.coordinate_eq_iff_orbit τ₁ τ₂).mp h
  obtain ⟨g, rfl⟩ := rhoTau_surjective a
  refine ⟨g, ?_⟩
  change rhoTauReal g • τ₁ = τ₂
  simpa [rhoTauReal, modularToReal] using ha

/-- Postcomposing an analytic upper-half-plane-valued germ by a modular deck transformation
again has an analytic complex representative. -/
theorem analyticAt_modularDeck_coe
    (g : Delta) {τ : ℂ → UpperHalfPlane} {z : ℂ}
    (hτ : AnalyticAt ℂ (fun w ↦ (τ w : ℂ)) z) :
    AnalyticAt ℂ (fun w ↦ (modularDeckHomeomorph g (τ w) : ℂ)) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [hτ.eventually_analyticAt] with w hw
  have hτmd : MDiffAt τ w := by
    have hcomp := (UpperHalfPlane.mdifferentiableAt_ofComplex (τ w).im_pos).comp w
      hw.differentiableAt.mdifferentiableAt
    exact hcomp.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun u ↦
      (UpperHalfPlane.ofComplex_apply (τ u)).symm
  have hdeckmd : MDiffAt (fun u ↦ modularDeckHomeomorph g (τ u)) w := by
    have hg : MDiff (fun u : UpperHalfPlane ↦ rhoTauReal g • u) :=
      UpperHalfPlane.mdifferentiable_smul (by simp [rhoTauReal, modularToReal])
    change MDiffAt (fun u ↦ rhoTauReal g • τ u) w
    exact hg.mdifferentiableAt.comp w hτmd
  have hcoe : MDiffAt (fun u ↦ (modularDeckHomeomorph g (τ u) : ℂ)) w :=
    UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt.comp w hdeckmd
  exact hcoe.differentiableAt

/-- The ordinary-value locus of the normalized modular quotient. -/
def modularRegularValueSet : Set ℂ := ({0, 1} : Set ℂ)ᶜ

/-- The target upper half-plane with its two elliptic fibers removed. -/
abbrev ModularRegularPoint :=
  {τ : UpperHalfPlane // normalizedModularJCoordinate τ ∈ modularRegularValueSet}

/-- The target modular quotient restricted to ordinary values. -/
def modularRegularCoordinate : ModularRegularPoint → modularRegularValueSet :=
  fun τ ↦ ⟨normalizedModularJCoordinate τ, τ.2⟩

/-- Exact modular uniformization supplies the covering used for uniqueness on the regular
locus. -/
theorem modularRegularCoordinate_isCoveringMap
    (J : ExactNormalizedModularJUniformization) :
    IsCoveringMap modularRegularCoordinate := by
  change IsCoveringMap
    (modularRegularValueSet.restrictPreimage normalizedModularJCoordinate)
  exact J.regular_covering.isCoveringMap_restrictPreimage

/-- Two analytic germs which agree frequently at punctured points agree near the puncture. -/
theorem eventuallyEq_of_analyticAt_of_frequently_eq
    {F G : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z)
    (hfreq : ∃ᶠ w in 𝓝[≠] z, F w = G w) :
    F =ᶠ[𝓝 z] G := by
  obtain ⟨rF, hrF, hFball⟩ := hF.exists_ball_analyticOnNhd
  obtain ⟨rG, hrG, hGball⟩ := hG.exists_ball_analyticOnNhd
  let W : Set ℂ := ball z rF ∩ ball z rG
  have hWo : IsOpen W := isOpen_ball.inter isOpen_ball
  have hzW : z ∈ W := ⟨mem_ball_self hrF, mem_ball_self hrG⟩
  have hWpre : IsPreconnected W :=
    (convex_ball z rF).inter (convex_ball z rG) |>.isPreconnected
  have hFW : AnalyticOnNhd ℂ F W := hFball.mono inter_subset_left
  have hGW : AnalyticOnNhd ℂ G W := hGball.mono inter_subset_right
  have heq := hFW.eqOn_of_preconnected_of_frequently_eq hGW hWpre hzW hfreq
  exact Filter.eventuallyEq_of_mem (hWo.mem_nhds hzW) heq

/-- **Punctured regular-locus uniqueness.**

Suppose two upper-half-plane-valued maps solve the same normalized modular equation on a
preconnected set `V`, all their values there are ordinary, and a fixed modular deck transform
has made them agree at one point of `V`.  Covering-lift uniqueness makes them equal on all of
`V`.  If `V` occurs frequently at the puncture and the complex representatives are analytic
there, the two germs at the puncture are equal.

The deck transformation itself is deliberately external to this lemma: callers apply it to
`τ₁` before invoking the result. -/
theorem eventuallyEq_of_regular_covering_lifts
    (J : ExactNormalizedModularJUniformization)
    {τ₁ τ₂ : ℂ → UpperHalfPlane} {V : Set ℂ} {z w₀ : ℂ}
    (hVpre : IsPreconnected V) (hw₀ : w₀ ∈ V)
    (hτ₁cont : ContinuousOn τ₁ V) (hτ₂cont : ContinuousOn τ₂ V)
    (hτ₁reg : ∀ w ∈ V,
      normalizedModularJCoordinate (τ₁ w) ∈ modularRegularValueSet)
    (hτ₂reg : ∀ w ∈ V,
      normalizedModularJCoordinate (τ₂ w) ∈ modularRegularValueSet)
    (hequation : ∀ w ∈ V,
      normalizedModularJCoordinate (τ₁ w) =
        normalizedModularJCoordinate (τ₂ w))
    (hmatch : τ₁ w₀ = τ₂ w₀)
    (hfreqV : ∃ᶠ w in 𝓝[≠] z, w ∈ V)
    (hτ₁an : AnalyticAt ℂ (fun w ↦ (τ₁ w : ℂ)) z)
    (hτ₂an : AnalyticAt ℂ (fun w ↦ (τ₂ w : ℂ)) z) :
    (fun w ↦ (τ₁ w : ℂ)) =ᶠ[𝓝 z] fun w ↦ (τ₂ w : ℂ) := by
  let L₁ : V → ModularRegularPoint :=
    fun w ↦ ⟨τ₁ w, hτ₁reg w w.2⟩
  let L₂ : V → ModularRegularPoint :=
    fun w ↦ ⟨τ₂ w, hτ₂reg w w.2⟩
  have hL₁ : Continuous L₁ := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp hτ₁cont
  have hL₂ : Continuous L₂ := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp hτ₂cont
  letI : PreconnectedSpace V := Subtype.preconnectedSpace hVpre
  have hbase : modularRegularCoordinate ∘ L₁ = modularRegularCoordinate ∘ L₂ := by
    funext w
    apply Subtype.ext
    exact hequation w w.2
  have hL : L₁ = L₂ :=
    (modularRegularCoordinate_isCoveringMap J).eq_of_comp_eq
      hL₁ hL₂ hbase ⟨w₀, hw₀⟩ (by
        apply Subtype.ext
        exact hmatch)
  have hEqOn : EqOn (fun w ↦ (τ₁ w : ℂ)) (fun w ↦ (τ₂ w : ℂ)) V := by
    intro w hw
    have h := congrArg (fun L : V → ModularRegularPoint ↦ L ⟨w, hw⟩) hL
    exact congrArg (fun τ : ModularRegularPoint ↦ (τ.1 : ℂ)) h
  apply eventuallyEq_of_analyticAt_of_frequently_eq hτ₁an hτ₂an
  exact hfreqV.mono fun w hw ↦ hEqOn hw

/-- A fixed modular transformation which matches two regular lifts at one point matches their
analytic germs across an isolated puncture.  This is the form used in the deck-transitivity
argument: exactness of the ordinary modular fiber supplies `g`, while this theorem proves that
the same `g` works on the whole punctured neighbourhood and at its missing center. -/
theorem eventuallyEq_modularDeck_of_regular_covering_lifts
    (J : ExactNormalizedModularJUniformization) (g : Delta)
    {τ₁ τ₂ : ℂ → UpperHalfPlane} {V : Set ℂ} {z w₀ : ℂ}
    (hVpre : IsPreconnected V) (hw₀ : w₀ ∈ V)
    (hτ₁cont : ContinuousOn τ₁ V) (hτ₂cont : ContinuousOn τ₂ V)
    (hτ₁reg : ∀ w ∈ V,
      normalizedModularJCoordinate (τ₁ w) ∈ modularRegularValueSet)
    (hτ₂reg : ∀ w ∈ V,
      normalizedModularJCoordinate (τ₂ w) ∈ modularRegularValueSet)
    (hequation : ∀ w ∈ V,
      normalizedModularJCoordinate (τ₁ w) =
        normalizedModularJCoordinate (τ₂ w))
    (hmatch : modularDeckHomeomorph g (τ₁ w₀) = τ₂ w₀)
    (hfreqV : ∃ᶠ w in 𝓝[≠] z, w ∈ V)
    (hτ₁an : AnalyticAt ℂ (fun w ↦ (τ₁ w : ℂ)) z)
    (hτ₂an : AnalyticAt ℂ (fun w ↦ (τ₂ w : ℂ)) z) :
    (fun w ↦ (modularDeckHomeomorph g (τ₁ w) : ℂ)) =ᶠ[𝓝 z]
      fun w ↦ (τ₂ w : ℂ) := by
  apply eventuallyEq_of_regular_covering_lifts J hVpre hw₀
      ((modularDeckHomeomorph g).continuous.continuousOn.comp hτ₁cont
        fun _ _ ↦ Set.mem_univ _)
      hτ₂cont
  · intro w hw
    simp only [Function.comp_apply]
    rw [normalizedModularJCoordinate_modularDeck]
    exact hτ₁reg w hw
  · exact hτ₂reg
  · intro w hw
    simp only [Function.comp_apply]
    rw [normalizedModularJCoordinate_modularDeck]
    exact hequation w hw
  · exact hmatch
  · exact hfreqV
  · exact analyticAt_modularDeck_coe g hτ₁an
  · exact hτ₂an


end SphereSixComplex.Periods.SolutionGermDeckTransitivity
