module

public import SphereSixComplex.Periods.Uniformization.NormalizedModularJContinuationCriterion
import all SphereSixComplex.Periods.Uniformization.NormalizedModularJContinuationCriterion
public import Mathlib.Analysis.Normed.Module.RCLike.Real
import all Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

/-!
# Producing the punctured regular comparison neighbourhood

The global continuation criterion only needs a connected set of ordinary points accumulating at
the center.  A small ball tangent to the center is enough; unlike a punctured disc, it is convex,
so no separate theorem about the fundamental group or connectedness of punctured discs is needed.
-/

noncomputable section

namespace SphereSixComplex.Periods.PuncturedRegularComparison

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped Manifold
open SphereSixComplex.TriangleGroup
open TauCeti
open SolutionGermDeckTransitivity SolutionGermModularDeck
open NormalizedModularJContinuationCriterion

/-- Every punctured neighbourhood in `ℂ` contains a convex tangent ball which accumulates at the
puncture. -/
theorem exists_preconnected_frequently_subset_of_mem_nhdsNE
    {s : Set ℂ} {z : ℂ} (hs : s ∈ 𝓝[≠] z) :
    ∃ V : Set ℂ, IsPreconnected V ∧ V ⊆ s ∧ (∃ᶠ w in 𝓝[≠] z, w ∈ V) := by
  have hs' : {w : ℂ | w ≠ z → w ∈ s} ∈ 𝓝 z :=
    eventually_nhdsWithin_iff.mp hs
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hs'
  let c : ℂ := z + (r / 2 : ℝ)
  let V : Set ℂ := ball c (r / 2)
  have hr2 : 0 < r / 2 := by positivity
  have hdist : dist c z = r / 2 := by
    simp [c, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hzV : z ∉ V := by
    change ¬dist z c < r / 2
    rw [dist_comm, hdist]
    exact lt_irrefl _
  have hVball : V ⊆ ball z r := by
    intro w hw
    change dist w c < r / 2 at hw
    rw [mem_ball]
    calc
      dist w z ≤ dist w c + dist c z := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [hdist]; linarith
      _ = r := by ring
  refine ⟨V, (convex_ball c (r / 2)).isPreconnected, ?_, ?_⟩
  · intro w hw
    exact hrsub (hVball hw) (fun hwz ↦ hzV (hwz ▸ hw))
  · rw [← mem_closure_ne_iff_frequently_within]
    have hdiff : V \ {z} = V := sdiff_eq_left.mpr (disjoint_singleton_right.mpr hzV)
    rw [hdiff]
    change z ∈ closure (ball c (r / 2))
    rw [closure_ball c hr2.ne']
    rw [mem_closedBall, dist_comm, hdist]

/-- If the source coordinate is ordinary throughout a punctured neighbourhood, then any two
solution germs over the center admit the comparison neighbourhood required by the global
criterion. -/
theorem hasPuncturedRegularComparison_of_eventually_regular
    {C : ℂ → ℂ} {U : Set ℂ} {p q : ModularSolutionEtale C U}
    (hbase : upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U p =
      upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate C U q)
    (hregular : ∀ᶠ w in 𝓝[≠] p.1.base, C w ∈ modularRegularValueSet) :
    HasPuncturedRegularComparison p q := by
  have hpqbase : p.1.base = q.1.base := congrArg Subtype.val hbase
  have hpeq := solutionRepresentative_equation_eventuallyEq p
  have hqeq :
      (fun w ↦ normalizedModularJCoordinate (solutionRepresentative q w)) =ᶠ[𝓝 p.1.base]
        C := by
    rw [hpqbase]
    exact solutionRepresentative_equation_eventuallyEq q
  have hpan : AnalyticAt ℂ (fun w ↦ (solutionRepresentative p w : ℂ)) p.1.base :=
    (HolomorphicPresheaf.analyticAt_repFun p.1).congr
      (solutionRepresentative_coe_eventuallyEq p).symm
  have hqan : AnalyticAt ℂ (fun w ↦ (solutionRepresentative q w : ℂ)) p.1.base := by
    rw [hpqbase]
    exact (HolomorphicPresheaf.analyticAt_repFun q.1).congr
      (solutionRepresentative_coe_eventuallyEq q).symm
  let good : Set ℂ := {w |
    C w ∈ modularRegularValueSet ∧
    normalizedModularJCoordinate (solutionRepresentative p w) = C w ∧
    normalizedModularJCoordinate (solutionRepresentative q w) = C w ∧
    AnalyticAt ℂ (fun u ↦ (solutionRepresentative p u : ℂ)) w ∧
    AnalyticAt ℂ (fun u ↦ (solutionRepresentative q u : ℂ)) w}
  have hgood : good ∈ 𝓝[≠] p.1.base := by
    filter_upwards [hregular, hpeq.filter_mono nhdsWithin_le_nhds,
      hqeq.filter_mono nhdsWithin_le_nhds,
      hpan.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      hqan.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with w hwreg hpw hqw hpwa hqwa
    exact ⟨hwreg, hpw, hqw, hpwa, hqwa⟩
  obtain ⟨V, hVpre, hVgood, hVfreq⟩ :=
    exists_preconnected_frequently_subset_of_mem_nhdsNE hgood
  have hpAnalytic : AnalyticOnNhd ℂ (fun w ↦ (solutionRepresentative p w : ℂ)) V :=
    fun w hw ↦ (hVgood hw).2.2.2.1
  have hqAnalytic : AnalyticOnNhd ℂ (fun w ↦ (solutionRepresentative q w : ℂ)) V :=
    fun w hw ↦ (hVgood hw).2.2.2.2
  have hpcont : ContinuousOn (solutionRepresentative p) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcbase := continuousOn_iff_continuous_domRestrict.mp hpAnalytic.continuousOn
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    have heq : UpperHalfPlane.coe ∘ V.domRestrict (solutionRepresentative p) =
        V.domRestrict (fun w ↦ (solutionRepresentative p w : ℂ)) := by
      funext w
      rfl
    rw [heq]
    exact hcbase
  have hqcont : ContinuousOn (solutionRepresentative q) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcbase := continuousOn_iff_continuous_domRestrict.mp hqAnalytic.continuousOn
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    have heq : UpperHalfPlane.coe ∘ V.domRestrict (solutionRepresentative q) =
        V.domRestrict (fun w ↦ (solutionRepresentative q w : ℂ)) := by
      funext w
      rfl
    rw [heq]
    exact hcbase
  have hVnonempty : V.Nonempty := by
    by_contra hVempty
    rw [not_nonempty_iff_eq_empty.mp hVempty] at hVfreq
    simpa using hVfreq
  obtain ⟨w₀, hw₀⟩ := hVnonempty
  refine ⟨V, w₀, hVpre, hw₀, hpcont, hqcont, ?_, ?_, ?_, hVfreq⟩
  · intro w hw
    rw [(hVgood hw).2.1]
    exact (hVgood hw).1
  · intro w hw
    rw [(hVgood hw).2.2.1]
    exact (hVgood hw).1
  · intro w hw
    exact (hVgood hw).2.1.trans (hVgood hw).2.2.1.symm

/-- The complex extension of an exact source coordinate is analytic throughout the upper
half-plane. -/
theorem sourceCoordinate_complex_analyticOnNhd
    (C : ExactFuchsianOrbifoldCoordinate) :
    AnalyticOnNhd ℂ (C.coordinate ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet := by
  rw [Complex.analyticOnNhd_iff_differentiableOn
    UpperHalfPlane.isOpen_upperHalfPlaneSet]
  intro z hz
  have hmd : MDiffAt (C.coordinate ∘ UpperHalfPlane.ofComplex) z :=
    (C.coordinate_holomorphic (UpperHalfPlane.ofComplex z)).comp z
      (UpperHalfPlane.mdifferentiableAt_ofComplex hz)
  exact hmd.differentiableAt.differentiableWithinAt

/-- An exact source coordinate avoids both elliptic values in every punctured neighbourhood.

This follows from isolated zeros and is slightly stronger than transporting the two displayed
branch charts around their orbits.  A locally constant zero (respectively one) would propagate by
the identity theorem across the connected upper half-plane and contradict the other normalized
elliptic value. -/
theorem sourceCoordinate_eventually_regular
    (C : ExactFuchsianOrbifoldCoordinate) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ∀ᶠ w in 𝓝[≠] z,
      C.coordinate (UpperHalfPlane.ofComplex w) ∈ modularRegularValueSet := by
  let F : ℂ → ℂ := C.coordinate ∘ UpperHalfPlane.ofComplex
  have hFan : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet :=
    sourceCoordinate_complex_analyticOnNhd C
  have hpre : IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hne0 : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 := by
    rcases (hFan z hz).eventually_eq_or_eventually_ne analyticAt_const with hlocal | hne
    · exfalso
      have hfreq : ∃ᶠ w in 𝓝[≠] z, F w = (fun _ : ℂ ↦ (0 : ℂ)) w :=
        (hlocal.filter_mono nhdsWithin_le_nhds).frequently
      have heq := hFan.eqOn_of_preconnected_of_frequently_eq
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (0 : ℂ))
          UpperHalfPlane.upperHalfPlaneSet) hpre hz hfreq
      have htwo := heq (x := (fuchsianTwoFixedPoint : ℂ))
        fuchsianTwoFixedPoint.im_pos
      have : C.coordinate fuchsianTwoFixedPoint = 0 := by
        simpa [F, UpperHalfPlane.ofComplex_apply] using htwo
      exact one_ne_zero (C.coordinate_at_two.symm.trans this)
    · simpa only [Pi.zero_apply] using hne
  have hne1 : ∀ᶠ w in 𝓝[≠] z, F w ≠ 1 := by
    rcases (hFan z hz).eventually_eq_or_eventually_ne analyticAt_const with hlocal | hne
    · exfalso
      have hfreq : ∃ᶠ w in 𝓝[≠] z, F w = (fun _ : ℂ ↦ (1 : ℂ)) w :=
        (hlocal.filter_mono nhdsWithin_le_nhds).frequently
      have heq := hFan.eqOn_of_preconnected_of_frequently_eq
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (1 : ℂ))
          UpperHalfPlane.upperHalfPlaneSet) hpre hz hfreq
      have hone := heq (x := (fuchsianOneFixedPoint : ℂ)) fuchsianOneFixedPoint.im_pos
      have : C.coordinate fuchsianOneFixedPoint = 1 := by
        simpa [F, UpperHalfPlane.ofComplex_apply] using hone
      exact zero_ne_one (C.coordinate_at_one.symm.trans this)
    · simpa using hne
  filter_upwards [hne0, hne1] with w hw0 hw1
  exact by simpa [F, modularRegularValueSet] using And.intro hw0 hw1

/-- Every pair of solution germs for an exact source coordinate has the punctured regular
comparison required for deck transitivity. -/
theorem exactSource_hasPuncturedRegularComparison
    (C : ExactFuchsianOrbifoldCoordinate)
    (p q : ModularSolutionEtale
      (C.coordinate ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet)
    (hbase : upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate
      (C.coordinate ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet p =
      upperHalfPlaneSolutionEtaleBase normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet q) :
    HasPuncturedRegularComparison p q := by
  apply hasPuncturedRegularComparison_of_eventually_regular hbase
  exact sourceCoordinate_eventually_regular C p.2.1

/-- For an exact source coordinate, pointwise local solutions are the only remaining input to
relation-preserving continuation; the global topology and deck transitivity are automatic. -/
theorem continuesInsideWith_of_exactSource_of_local_solutions
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate)
    {f₀ : ℂ → ℂ} {z₀ : ℂ}
    (hz₀ : z₀ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hf₀ : AnalyticAt ℂ f₀ z₀)
    (hP₀ : IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
      (C.coordinate ∘ UpperHalfPlane.ofComplex) z₀ f₀)
    (hlocal : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
        IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
          (C.coordinate ∘ UpperHalfPlane.ofComplex) z f) :
    ContinuesInsideWith f₀ UpperHalfPlane.upperHalfPlaneSet z₀
      (IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex)) := by
  apply continuesInsideWith_of_punctured_regular_comparison J
    UpperHalfPlane.isOpen_upperHalfPlaneSet hz₀ hf₀ hP₀ hlocal
  intro p q hpq
  exact exactSource_hasPuncturedRegularComparison C p q hpq


end SphereSixComplex.Periods.PuncturedRegularComparison
