module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Meromorphic.NormalForm
import all Mathlib.Analysis.Complex.BranchLogRoot
import all Mathlib.Analysis.Calculus.Deriv.Slope
import all Mathlib.Analysis.Complex.CauchyIntegral
import all Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import all Mathlib.Analysis.Convex.Contractible
import all Mathlib.Analysis.Meromorphic.NormalForm

open Filter Set
open scoped Topology

namespace SphereSixComplex.Periods.AnalyticSquareRoot

/-- A continuous square root of a differentiable function is differentiable wherever it is
nonzero. -/
public lemma differentiableAt_of_continuousAt_sq_eq
    {r q : ℂ → ℂ} {z : ℂ}
    (hr : ContinuousAt r z) (hq : DifferentiableAt ℂ q z)
    (hrne : r z ≠ 0) (hsq : ∀ w, r w ^ 2 = q w) :
    DifferentiableAt ℂ r z := by
  have hden : Tendsto (fun w ↦ r w + r z) (𝓝[≠] z) (𝓝 (r z + r z)) :=
    (hr.tendsto.mono_left inf_le_left).add tendsto_const_nhds
  have hdenne : r z + r z ≠ 0 := by
    intro h
    apply hrne
    linear_combination h / 2
  have hquot : Tendsto
      (fun w ↦ slope q z w / (r w + r z)) (𝓝[≠] z)
      (𝓝 (deriv q z / (r z + r z))) :=
    hq.hasDerivAt.tendsto_slope.div hden hdenne
  have hden_event : ∀ᶠ w in 𝓝[≠] z, r w + r z ≠ 0 :=
    hden.eventually (isOpen_compl_singleton.mem_nhds hdenne)
  have hrderiv : HasDerivAt r (deriv q z / (r z + r z)) z := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    apply hquot.congr'
    filter_upwards [self_mem_nhdsWithin, hden_event] with w hw hwden
    rw [slope_def_field, slope_def_field]
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
    rw [← hsq w, ← hsq z]
    field_simp [hwz, hwden]
    ring
  exact hrderiv.differentiableAt

/-- A nowhere-zero analytic function on an open simply connected complex domain has an analytic
square root. `BranchLogRoot` supplies the continuous lift; differentiating its square identity
promotes it to a holomorphic lift. -/
public theorem exists_analyticOnNhd_sq_eq
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q U)
    (hqne : ∀ z ∈ U, q z ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r U ∧ ∀ z, r z ^ 2 = q z := by
  have hzero : 0 ∉ q '' U := by
    rintro ⟨z, hz, hzq⟩
    exact hqne z hz hzq
  obtain ⟨r, hrcont, hrsq⟩ := Complex.exists_continuousOn_pow_eq
    hUc hUo hq.continuousOn hzero (n := 2) (by norm_num)
  refine ⟨r, ?_, hrsq⟩
  apply DifferentiableOn.analyticOnNhd _ hUo
  intro z hz
  have hrz : ContinuousAt r z := hrcont.continuousAt (hUo.mem_nhds hz)
  have hrne : r z ≠ 0 := by
    intro hrzero
    have := hrsq z
    rw [hrzero, zero_pow (by norm_num)] at this
    exact hqne z hz this.symm
  exact differentiableAt_of_continuousAt_sq_eq hrz
    (hq z hz).differentiableAt hrne hrsq |>.differentiableWithinAt

/-- Replacing a meromorphic quotient of order zero by its normal-form representative produces a
nowhere-zero analytic function without changing it on punctured neighbourhoods. -/
public theorem toMeromorphicNFOn_analytic_ne_zero_of_order_zero
    {U : Set ℂ} {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (horder : ∀ z ∈ U, meromorphicOrderAt f z = 0) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn f U) U ∧
      (∀ z ∈ U, toMeromorphicNFOn f U z ≠ 0) ∧
      ∀ z ∈ U, toMeromorphicNFOn f U =ᶠ[𝓝[≠] z] f := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hnf := meromorphicNFOn_toMeromorphicNFOn f U hz
    apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hf hz, horder z hz]
  · intro z hz
    have hnf := meromorphicNFOn_toMeromorphicNFOn f U hz
    apply hnf.meromorphicOrderAt_eq_zero_iff.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hf hz, horder z hz]
  · intro z hz
    exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz

/-- The upper half-plane is simply connected. -/
public lemma upperHalfPlaneSet_isSimplyConnected :
    IsSimplyConnected UpperHalfPlane.upperHalfPlaneSet := by
  let := (convex_halfSpace_im_gt 0).contractibleSpace
    (show UpperHalfPlane.upperHalfPlaneSet.Nonempty from
      ⟨Complex.I, by simp [UpperHalfPlane.upperHalfPlaneSet]⟩)
  change SimplyConnectedSpace UpperHalfPlane.upperHalfPlaneSet
  infer_instance

end SphereSixComplex.Periods.AnalyticSquareRoot
