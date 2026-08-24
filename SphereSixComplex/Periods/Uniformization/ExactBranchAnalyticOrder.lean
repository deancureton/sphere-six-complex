module

public import SphereSixComplex.Periods.FuchsianModularParameterExistence
import all SphereSixComplex.Periods.FuchsianModularParameterExistence

@[expose] public section

noncomputable section

namespace SphereSixComplex.Periods

open Complex Filter Function Set Topology
open scoped Manifold

namespace HasExactHolomorphicBranchAt

variable {f : UpperHalfPlane → ℂ} {center : UpperHalfPlane}
  {value : ℂ} {order : ℕ}

/-- The branch expressed in the inverse of its supplied local uniformizer. -/
def complexGerm (h : HasExactHolomorphicBranchAt f center value order) : ℂ → ℂ :=
  (f ∘ h.uniformizer_isLocalDiffeomorph.localInverse) - fun _ ↦ value

/-- The branch unit pulled back through the inverse uniformizer. -/
def complexUnit (h : HasExactHolomorphicBranchAt f center value order) : ℂ → ℂ :=
  h.unit ∘ h.uniformizer_isLocalDiffeomorph.localInverse

private theorem localInverse_zero (h : HasExactHolomorphicBranchAt f center value order) :
    h.uniformizer_isLocalDiffeomorph.localInverse 0 = center := by
  have hleft := h.uniformizer_isLocalDiffeomorph.localInverse_left_inv
    h.uniformizer_isLocalDiffeomorph.localInverse_mem_target
  simpa [h.uniformizer_center] using hleft

private theorem localInverse_mdifferentiableAt_zero
    (h : HasExactHolomorphicBranchAt f center value order) :
    MDiffAt h.uniformizer_isLocalDiffeomorph.localInverse 0 := by
  simpa [h.uniformizer_center] using
    h.uniformizer_isLocalDiffeomorph.localInverse_mdifferentiableAt (by simp)

theorem complexUnit_zero_ne (h : HasExactHolomorphicBranchAt f center value order) :
    h.complexUnit 0 ≠ 0 := by
  simpa [complexUnit, h.localInverse_zero] using h.unit_ne_zero

theorem complexGerm_factorization (h : HasExactHolomorphicBranchAt f center value order) :
    ∀ᶠ w in 𝓝 0, h.complexGerm w = w ^ order * h.complexUnit w := by
  have hinv := h.localInverse_mdifferentiableAt_zero
  have hinvT : Tendsto h.uniformizer_isLocalDiffeomorph.localInverse
      (𝓝 0) (𝓝 center) := by
    simpa only [ContinuousAt, h.localInverse_zero] using hinv.continuousAt
  have hfac := hinvT h.factorization
  have hright :
      h.uniformizer ∘ h.uniformizer_isLocalDiffeomorph.localInverse =ᶠ[𝓝 0] id := by
    simpa [h.uniformizer_center] using
      h.uniformizer_isLocalDiffeomorph.localInverse_eventuallyEq_right
  filter_upwards [hfac, hright] with w hw hwr
  simpa [complexGerm, complexUnit, Function.comp_apply] using hw.trans
    (congrArg (fun v : ℂ ↦ v ^ order * h.unit
      (h.uniformizer_isLocalDiffeomorph.localInverse w)) hwr)

theorem complexGerm_analyticAt (h : HasExactHolomorphicBranchAt f center value order)
    (hf : MDiff f) : AnalyticAt ℂ h.complexGerm 0 := by
  have hinvOn :=
    h.uniformizer_isLocalDiffeomorph.localInverse_contMDiffOn.mdifferentiableOn (by simp)
  have hdiff : DifferentiableOn ℂ h.complexGerm
      h.uniformizer_isLocalDiffeomorph.localInverse.source := by
    intro w hw
    have hinvAt := hinvOn.mdifferentiableAt
      (h.uniformizer_isLocalDiffeomorph.localInverse.open_source.mem_nhds hw)
    have hmd : MDiffAt h.complexGerm w := by
      simpa [complexGerm, Function.comp_def] using
        ((hf (h.uniformizer_isLocalDiffeomorph.localInverse w)).comp w hinvAt).sub
          mdifferentiableAt_const
    have hd : DifferentiableAt ℂ h.complexGerm w := hmd.differentiableAt
    exact hd.differentiableWithinAt
  apply hdiff.analyticAt
  exact h.uniformizer_isLocalDiffeomorph.localInverse.open_source.mem_nhds (by
    simpa [h.uniformizer_center] using
      h.uniformizer_isLocalDiffeomorph.localInverse_mem_source)

/-- Although the branch contract only asks for `MDiffAt` of its displayed unit, the global
holomorphicity of `f` plus the factorization makes the pulled unit holomorphic: off zero it is the
quotient `complexGerm / z^order`, and continuity removes the singularity. -/
theorem complexUnit_analyticAt (h : HasExactHolomorphicBranchAt f center value order)
    (hf : MDiff f) : AnalyticAt ℂ h.complexUnit 0 := by
  have hinv := h.localInverse_mdifferentiableAt_zero
  have hunitAt : MDiffAt h.unit (h.uniformizer_isLocalDiffeomorph.localInverse 0) := by
    rw [h.localInverse_zero]
    exact h.unit_holomorphic
  have huCont : ContinuousAt h.complexUnit 0 := by
    simpa [complexUnit, Function.comp_def] using (hunitAt.comp 0 hinv).continuousAt
  obtain ⟨V, hVeq, hVo, hV0⟩ := eventually_nhds_iff.mp h.complexGerm_factorization
  have hAan := h.complexGerm_analyticAt hf
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ huCont
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hVo.mem_nhds hV0, hAan.eventually_analyticAt] with w hwV hAw hw0
  have hwne : w ≠ 0 := by simpa using hw0
  have hQdiff : DifferentiableAt ℂ (fun y ↦ h.complexGerm y / y ^ order) w :=
    hAw.differentiableAt.div (differentiableAt_id.pow order) (pow_ne_zero order hwne)
  apply hQdiff.congr_of_eventuallyEq
  filter_upwards [hVo.mem_nhds hwV, isOpen_ne.mem_nhds hwne] with y hyV hyne
  apply (eq_div_iff (pow_ne_zero order hyne)).2
  rw [mul_comm]
  exact (hVeq y hyV).symm

/-- The manifold branch contract has exactly the advertised analytic order after passing to its
own inverse uniformizer. -/
theorem complexGerm_analyticOrderAt (h : HasExactHolomorphicBranchAt f center value order) :
    MDiff f → analyticOrderAt h.complexGerm 0 = order := by
  intro hf
  apply (h.complexGerm_analyticAt hf).analyticOrderAt_eq_natCast.mpr
  refine ⟨h.complexUnit, h.complexUnit_analyticAt hf, h.complexUnit_zero_ne, ?_⟩
  simpa [sub_zero, smul_eq_mul] using h.complexGerm_factorization


end HasExactHolomorphicBranchAt

end SphereSixComplex.Periods
