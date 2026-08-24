module

public import SphereSixComplex.Periods.Uniformization.PuncturedRegularComparison
import all SphereSixComplex.Periods.Uniformization.PuncturedRegularComparison
public import SphereSixComplex.Periods.Uniformization.ExactEllipticLocalLifts
import all SphereSixComplex.Periods.Uniformization.ExactEllipticLocalLifts
public import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import all TauCeti.Analysis.Complex.UpperHalfPlane.Manifold

@[expose] public section

/-!
# Pointwise local solutions of the normalized modular equation

Ordinary points are lifted through one sheet of the exact modular covering.  The sheet is
converted into a complex biholomorphic partial inverse using Tau Ceti's injective-holomorphic-map
API.  The elliptic points are treated below using the exact power-chart lifts.
-/

noncomputable section

namespace SphereSixComplex.Periods.LocalModularJSolutions

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped Manifold
open SphereSixComplex.TriangleGroup
open TauCeti
open SolutionGermDeckTransitivity
open PuncturedRegularComparison

/-- A branch uniformizer, read in the ambient complex coordinate, is analytic at its branch
center. -/
theorem branchUniformizer_comp_ofComplex_analyticAt
    {G : UpperHalfPlane → ℂ} {center : UpperHalfPlane} {value : ℂ} {order : ℕ}
    (h : HasExactHolomorphicBranchAt G center value order) :
    AnalyticAt ℂ (h.uniformizer ∘ UpperHalfPlane.ofComplex) (center : ℂ) := by
  have huAt : CMDiffAt ⊤ h.uniformizer center :=
    h.uniformizer_isLocalDiffeomorph.contMDiffAt
  have huAt' : CMDiffAt ⊤ h.uniformizer
      (UpperHalfPlane.ofComplex (center : ℂ)) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using huAt
  exact (huAt'.comp (center : ℂ)
    (UpperHalfPlane.contMDiffAt_ofComplex center.im_pos)).contDiffAt.analyticAt

/-- The complex representative of a branch chart's chosen local inverse is analytic at the
origin. -/
theorem branchLocalInverse_coe_analyticAt
    {G : UpperHalfPlane → ℂ} {center : UpperHalfPlane} {value : ℂ} {order : ℕ}
    (h : HasExactHolomorphicBranchAt G center value order) :
    AnalyticAt ℂ (fun w ↦
      (h.uniformizer_isLocalDiffeomorph.localInverse w : ℂ)) 0 := by
  let e := h.uniformizer_isLocalDiffeomorph.localInverse
  have h0source : 0 ∈ e.source := by
    simpa [h.uniformizer_center] using
      h.uniformizer_isLocalDiffeomorph.localInverse_mem_source
  have hdiff : DifferentiableOn ℂ (fun w ↦ (e w : ℂ)) e.source := by
    intro w hw
    have heMD : MDiffAt e w := e.mdifferentiableAt (by simp) hw
    exact (UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt.comp w heMD)
      |>.differentiableAt.differentiableWithinAt
  exact hdiff.analyticAt (e.open_source.mem_nhds h0source)

/-- The ambient-complex germ of a source deck transformation. -/
def sourceActionComplex (g : Delta) : ℂ → ℂ :=
  fun w ↦ (fuchsianSourceAction g • UpperHalfPlane.ofComplex w : UpperHalfPlane)

theorem sourceActionComplex_analyticAt (g : Delta) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    AnalyticAt ℂ (sourceActionComplex g) z := by
  have hact : MDiff (fun τ : UpperHalfPlane ↦
      fuchsianSourceAction g • τ) :=
    (fuchsianSourceAction_contMDiff g 1).mdifferentiable (by norm_num)
  have hcoe : MDiff (fun τ : UpperHalfPlane ↦
      (fuchsianSourceAction g • τ : UpperHalfPlane)) := hact
  have hcomplex : MDiff (fun τ : UpperHalfPlane ↦
      ((fuchsianSourceAction g • τ : UpperHalfPlane) : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp hcoe
  exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcomplex hz

/-- Transporting a local solution along a source deck transformation gives a local solution at
the transported point. -/
theorem transport_localSolution_along_sourceAction
    (C : ExactFuchsianOrbifoldCoordinate) (g : Delta)
    {x y : UpperHalfPlane} (hxy : fuchsianSourceAction g • x = y)
    {f : ℂ → ℂ} (hfan : AnalyticAt ℂ f (x : ℂ))
    (hP : IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
      (C.coordinate ∘ UpperHalfPlane.ofComplex) (x : ℂ) f) :
    ∃ f' : ℂ → ℂ, AnalyticAt ℂ f' (y : ℂ) ∧
      IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex) (y : ℂ) f' := by
  let a : ℂ → ℂ := sourceActionComplex g⁻¹
  have haAn : AnalyticAt ℂ a (y : ℂ) :=
    sourceActionComplex_analyticAt g⁻¹ y.im_pos
  have haValue : a (y : ℂ) = (x : ℂ) := by
    apply congrArg ((↑) : UpperHalfPlane → ℂ)
    change fuchsianSourceAction g⁻¹ • UpperHalfPlane.ofComplex (y : ℂ) = x
    rw [UpperHalfPlane.ofComplex_apply, ← hxy, map_inv]
    exact (fuchsianSourceAction g).symm_apply_apply x
  have hfAt : AnalyticAt ℂ f (a (y : ℂ)) := by rw [haValue]; exact hfan
  let f' : ℂ → ℂ := f ∘ a
  have hf'An : AnalyticAt ℂ f' (y : ℂ) := hfAt.comp haAn
  obtain ⟨τ, hτf, hτeq⟩ := hP
  let τ' : ℂ → UpperHalfPlane := τ ∘ a
  have haTend : Tendsto a (𝓝 (y : ℂ)) (𝓝 (x : ℂ)) := by
    have h := haAn.continuousAt
    change Tendsto a (𝓝 (y : ℂ)) (𝓝 (a (y : ℂ))) at h
    rw [haValue] at h
    exact h
  refine ⟨f', hf'An, τ', ?_, ?_⟩
  · exact hτf.comp_tendsto haTend
  · apply Filter.EventuallyEq.trans (hτeq.comp_tendsto haTend)
    filter_upwards [] with w
    change C.coordinate (UpperHalfPlane.ofComplex (a w)) =
      C.coordinate (UpperHalfPlane.ofComplex w)
    have haUHP : UpperHalfPlane.ofComplex (a w) =
        fuchsianSourceAction g⁻¹ • UpperHalfPlane.ofComplex w := by
      exact UpperHalfPlane.ofComplex_apply _
    rw [haUHP]
    exact C.coordinate_invariant g⁻¹ (UpperHalfPlane.ofComplex w)

/-- A regular source value admits a local analytic upper-half-plane-valued solution of the exact
normalized modular equation. -/
theorem exists_regular_localSolution
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hzreg : C.coordinate (UpperHalfPlane.ofComplex z) ∈ modularRegularValueSet) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex) z f := by
  let A : ℂ → ℂ := C.coordinate ∘ UpperHalfPlane.ofComplex
  let F : ℂ → ℂ := normalizedModularJCoordinate ∘ UpperHalfPlane.ofComplex
  obtain ⟨τ₀, hτ₀⟩ := J.coordinate_isQuotientMap.surjective (A z)
  have hτ₀reg : normalizedModularJCoordinate τ₀ ∈ modularRegularValueSet := by
    rw [hτ₀]
    exact hzreg
  obtain ⟨e, hτ₀e, he⟩ := J.regular_covering.isLocalHomeomorphOn τ₀ hτ₀reg
  let W : Set ℂ := ((↑) : UpperHalfPlane → ℂ) '' e.source
  have hWopen : IsOpen W :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap e.source e.open_source
  have hτ₀W : (τ₀ : ℂ) ∈ W := ⟨τ₀, hτ₀e, rfl⟩
  have hFdiff : DifferentiableOn ℂ F W := by
    rintro w ⟨τ, hτe, rfl⟩
    exact (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex
      normalizedModularJCoordinate_holomorphic τ.im_pos).differentiableAt.differentiableWithinAt
  have hFinj : InjOn F W := by
    rintro _ ⟨τ, hτe, rfl⟩ _ ⟨υ, hυe, rfl⟩ hJ
    have hJ' : normalizedModularJCoordinate τ = normalizedModularJCoordinate υ := by
      simpa only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hJ
    have hτυ : τ = υ := e.injOn hτe hυe (by simpa only [← he] using hJ')
    exact congrArg ((↑) : UpperHalfPlane → ℂ) hτυ
  let b : OpenPartialHomeomorph ℂ ℂ :=
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph hFdiff hWopen hFinj
  have hbsource : b.source = W :=
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph_source hFdiff hWopen hFinj
  have hbtarget : b.target = F '' W :=
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph_target hFdiff hWopen hFinj
  have hAz : A z = F (τ₀ : ℂ) := by
    simp only [A, F, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact hτ₀.symm
  have hAzTarget : A z ∈ b.target := by
    rw [hbtarget, hAz]
    exact ⟨(τ₀ : ℂ), hτ₀W, rfl⟩
  let f : ℂ → ℂ := b.symm ∘ A
  have hAan : AnalyticAt ℂ A z :=
    (sourceCoordinate_complex_analyticOnNhd C) z hz
  have hbinv : DifferentiableOn ℂ b.symm b.target := by
    rw [hbtarget]
    exact TauCeti.DifferentiableOn.differentiableOn_toOpenPartialHomeomorph_symm
      hFdiff hWopen hFinj
  have hbinvAn : AnalyticAt ℂ b.symm (A z) :=
    hbinv.analyticAt (b.open_target.mem_nhds hAzTarget)
  have hfan : AnalyticAt ℂ f z := hbinvAn.comp hAan
  have hAevent : ∀ᶠ w in 𝓝 z, A w ∈ b.target :=
    hAan.continuousAt (b.open_target.mem_nhds hAzTarget)
  have hfW : ∀ᶠ w in 𝓝 z, f w ∈ W := by
    filter_upwards [hAevent] with w hw
    rw [← hbsource]
    exact b.map_target hw
  have hfIm : ∀ᶠ w in 𝓝 z, 0 < (f w).im := by
    filter_upwards [hfW] with w hw
    obtain ⟨τ, -, hτ⟩ := hw
    rw [← hτ]
    exact τ.im_pos
  let τ : ℂ → UpperHalfPlane := fun w ↦ UpperHalfPlane.ofComplex (f w)
  refine ⟨f, hfan, τ, ?_, ?_⟩
  · filter_upwards [hfIm] with w hw
    exact congrArg ((↑) : UpperHalfPlane → ℂ)
      (UpperHalfPlane.ofComplex_apply_of_im_pos hw)
  · filter_upwards [hAevent, hfIm] with w hAw hfw
    have hright := b.right_inv hAw
    have hF : F (f w) = A w := by
      simpa [f, b, TauCeti.DifferentiableOn.toOpenPartialHomeomorph_apply]
        using hright
    have hτ : τ w = ⟨f w, hfw⟩ :=
      UpperHalfPlane.ofComplex_apply_of_im_pos hfw
    change normalizedModularJCoordinate (τ w) = A w
    rw [hτ]
    exact (by
      simpa [F, UpperHalfPlane.ofComplex_apply_of_im_pos hfw] using hF)

/-- The canonical order-three source point has a local solution obtained from the exact `3 → 3`
power-chart lift. -/
theorem exists_orderThree_localSolution_at_center
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f (fuchsianOneFixedPoint : ℂ) ∧
      IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex) (fuchsianOneFixedPoint : ℂ) f := by
  obtain ⟨r, hr, L, hLan, hL0, hchart⟩ := exists_exact_orderThree_chartLift J C
  let s : ℂ → ℂ := C.branch_one.uniformizer ∘ UpperHalfPlane.ofComplex
  let t : ℂ → ℂ := L ∘ s
  let τ : ℂ → UpperHalfPlane := fun w ↦
    J.branch_three.uniformizer_isLocalDiffeomorph.localInverse (t w)
  let f : ℂ → ℂ := fun w ↦ (τ w : ℂ)
  have hs0 : s (fuchsianOneFixedPoint : ℂ) = 0 := by
    simp [s, UpperHalfPlane.ofComplex_apply, C.branch_one.uniformizer_center]
  have hsAn : AnalyticAt ℂ s (fuchsianOneFixedPoint : ℂ) :=
    branchUniformizer_comp_ofComplex_analyticAt C.branch_one
  have hLAn : AnalyticAt ℂ L 0 := hLan 0 (mem_ball_self hr)
  have hLAn' : AnalyticAt ℂ L (s (fuchsianOneFixedPoint : ℂ)) := by
    rw [hs0]
    exact hLAn
  have htAn : AnalyticAt ℂ t (fuchsianOneFixedPoint : ℂ) := by
    exact hLAn'.comp hsAn
  have ht0 : t (fuchsianOneFixedPoint : ℂ) = 0 := by simp [t, hs0, hL0]
  have hinvAn : AnalyticAt ℂ
      (fun w ↦ (J.branch_three.uniformizer_isLocalDiffeomorph.localInverse w : ℂ))
      (t (fuchsianOneFixedPoint : ℂ)) := by
    rw [ht0]
    exact branchLocalInverse_coe_analyticAt J.branch_three
  have hfAn : AnalyticAt ℂ f (fuchsianOneFixedPoint : ℂ) := hinvAn.comp htAn
  have hsBall : ∀ᶠ w in 𝓝 (fuchsianOneFixedPoint : ℂ), s w ∈ ball 0 r :=
    hsAn.continuousAt (hs0.symm ▸ isOpen_ball.mem_nhds (mem_ball_self hr))
  have hofTend : Tendsto UpperHalfPlane.ofComplex
      (𝓝 (fuchsianOneFixedPoint : ℂ)) (𝓝 fuchsianOneFixedPoint) := by
    have h :=
      (UpperHalfPlane.mdifferentiableAt_ofComplex fuchsianOneFixedPoint.im_pos).continuousAt
    change Tendsto UpperHalfPlane.ofComplex (𝓝 (fuchsianOneFixedPoint : ℂ))
      (𝓝 (UpperHalfPlane.ofComplex (fuchsianOneFixedPoint : ℂ))) at h
    rw [UpperHalfPlane.ofComplex_apply] at h
    exact h
  have hsrcLeft :
      (fun w ↦ C.branch_one.uniformizer_isLocalDiffeomorph.localInverse (s w)) =ᶠ[
        𝓝 (fuchsianOneFixedPoint : ℂ)] UpperHalfPlane.ofComplex := by
    simpa only [s, Function.comp_apply, Function.comp_def, id_eq] using
      C.branch_one.uniformizer_isLocalDiffeomorph.localInverse_eventuallyEq_left.comp_tendsto
        hofTend
  refine ⟨f, hfAn, τ, Filter.EventuallyEq.rfl, ?_⟩
  filter_upwards [hsBall, hsrcLeft] with w hsw hleft
  have h := hchart (s w) hsw
  simp only [HasExactHolomorphicBranchAt.complexGerm, Pi.sub_apply,
    Function.comp_apply, sub_zero] at h
  change normalizedModularJCoordinate (τ w) =
    C.coordinate (UpperHalfPlane.ofComplex w)
  change normalizedModularJCoordinate
    (J.branch_three.uniformizer_isLocalDiffeomorph.localInverse (t w)) = _
  rw [← hleft]
  exact h

/-- The canonical order-four source point has a local solution obtained from the exact `4 → 2`
power-chart lift. -/
theorem exists_orderFourTwo_localSolution_at_center
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f (fuchsianTwoFixedPoint : ℂ) ∧
      IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex) (fuchsianTwoFixedPoint : ℂ) f := by
  obtain ⟨r, hr, L, hLan, hL0, hchart⟩ := exists_exact_orderFourTwo_chartLift J C
  let s : ℂ → ℂ := C.branch_two.uniformizer ∘ UpperHalfPlane.ofComplex
  let t : ℂ → ℂ := L ∘ s
  let τ : ℂ → UpperHalfPlane := fun w ↦
    J.branch_two.uniformizer_isLocalDiffeomorph.localInverse (t w)
  let f : ℂ → ℂ := fun w ↦ (τ w : ℂ)
  have hs0 : s (fuchsianTwoFixedPoint : ℂ) = 0 := by
    simp [s, UpperHalfPlane.ofComplex_apply, C.branch_two.uniformizer_center]
  have hsAn : AnalyticAt ℂ s (fuchsianTwoFixedPoint : ℂ) :=
    branchUniformizer_comp_ofComplex_analyticAt C.branch_two
  have hLAn : AnalyticAt ℂ L 0 := hLan 0 (mem_ball_self hr)
  have hLAn' : AnalyticAt ℂ L (s (fuchsianTwoFixedPoint : ℂ)) := by
    rw [hs0]
    exact hLAn
  have htAn : AnalyticAt ℂ t (fuchsianTwoFixedPoint : ℂ) := hLAn'.comp hsAn
  have ht0 : t (fuchsianTwoFixedPoint : ℂ) = 0 := by simp [t, hs0, hL0]
  have hinvAn : AnalyticAt ℂ
      (fun w ↦ (J.branch_two.uniformizer_isLocalDiffeomorph.localInverse w : ℂ))
      (t (fuchsianTwoFixedPoint : ℂ)) := by
    rw [ht0]
    exact branchLocalInverse_coe_analyticAt J.branch_two
  have hfAn : AnalyticAt ℂ f (fuchsianTwoFixedPoint : ℂ) := hinvAn.comp htAn
  have hsBall : ∀ᶠ w in 𝓝 (fuchsianTwoFixedPoint : ℂ), s w ∈ ball 0 r :=
    hsAn.continuousAt (hs0.symm ▸ isOpen_ball.mem_nhds (mem_ball_self hr))
  have hofTend : Tendsto UpperHalfPlane.ofComplex
      (𝓝 (fuchsianTwoFixedPoint : ℂ)) (𝓝 fuchsianTwoFixedPoint) := by
    have h :=
      (UpperHalfPlane.mdifferentiableAt_ofComplex fuchsianTwoFixedPoint.im_pos).continuousAt
    change Tendsto UpperHalfPlane.ofComplex (𝓝 (fuchsianTwoFixedPoint : ℂ))
      (𝓝 (UpperHalfPlane.ofComplex (fuchsianTwoFixedPoint : ℂ))) at h
    rw [UpperHalfPlane.ofComplex_apply] at h
    exact h
  have hsrcLeft :
      (fun w ↦ C.branch_two.uniformizer_isLocalDiffeomorph.localInverse (s w)) =ᶠ[
        𝓝 (fuchsianTwoFixedPoint : ℂ)] UpperHalfPlane.ofComplex := by
    simpa only [s, Function.comp_apply, Function.comp_def, id_eq] using
      C.branch_two.uniformizer_isLocalDiffeomorph.localInverse_eventuallyEq_left.comp_tendsto
        hofTend
  refine ⟨f, hfAn, τ, Filter.EventuallyEq.rfl, ?_⟩
  filter_upwards [hsBall, hsrcLeft] with w hsw hleft
  have h := hchart (s w) hsw
  simp only [HasExactHolomorphicBranchAt.complexGerm, Pi.sub_apply,
    Function.comp_apply] at h
  change normalizedModularJCoordinate (τ w) =
    C.coordinate (UpperHalfPlane.ofComplex w)
  change normalizedModularJCoordinate
    (J.branch_two.uniformizer_isLocalDiffeomorph.localInverse (t w)) = _
  rw [← hleft]
  change normalizedModularJCoordinate
      (J.branch_two.uniformizer_isLocalDiffeomorph.localInverse (t w)) - 1 =
    C.coordinate (C.branch_two.uniformizer_isLocalDiffeomorph.localInverse (s w)) - 1 at h
  exact sub_left_injective h

/-- Every point of the source upper half-plane admits a local analytic solution of the normalized
modular equation. -/
theorem exists_localSolution
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) (z : ℂ)
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
        (C.coordinate ∘ UpperHalfPlane.ofComplex) z f := by
  let y : UpperHalfPlane := UpperHalfPlane.ofComplex z
  have hyz : (y : ℂ) = z := by
    exact congrArg ((↑) : UpperHalfPlane → ℂ)
      (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
  by_cases h0 : C.coordinate y = 0
  · have hcoord : C.coordinate fuchsianOneFixedPoint = C.coordinate y :=
      C.coordinate_at_one.trans h0.symm
    obtain ⟨g, hg⟩ := (C.coordinate_eq_iff_orbit fuchsianOneFixedPoint y).mp hcoord
    obtain ⟨f, hfan, hP⟩ := exists_orderThree_localSolution_at_center J C
    rw [← hyz]
    exact transport_localSolution_along_sourceAction C g hg hfan hP
  by_cases h1 : C.coordinate y = 1
  · have hcoord : C.coordinate fuchsianTwoFixedPoint = C.coordinate y :=
      C.coordinate_at_two.trans h1.symm
    obtain ⟨g, hg⟩ := (C.coordinate_eq_iff_orbit fuchsianTwoFixedPoint y).mp hcoord
    obtain ⟨f, hfan, hP⟩ := exists_orderFourTwo_localSolution_at_center J C
    rw [← hyz]
    exact transport_localSolution_along_sourceAction C g hg hfan hP
  apply exists_regular_localSolution J C hz
  simp only [modularRegularValueSet, mem_compl_iff, mem_insert_iff,
    mem_singleton_iff, not_or]
  exact ⟨h0, h1⟩


end SphereSixComplex.Periods.LocalModularJSolutions
