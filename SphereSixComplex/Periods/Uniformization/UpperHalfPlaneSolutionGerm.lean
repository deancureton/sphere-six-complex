module

public import SphereSixComplex.Periods.Uniformization.GlobalBranchWithPredicate
import all SphereSixComplex.Periods.Uniformization.GlobalBranchWithPredicate
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import all Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

@[expose] public section

noncomputable section

namespace TauCeti

open Filter Set Topology
open scoped Manifold

/-- A germ of a complex-valued function locally represented by an upper-half-plane-valued
solution of `j ∘ τ = C`.  Keeping the representative existential avoids making an arbitrary
total extension of `j` outside the upper half-plane. -/
def IsUpperHalfPlaneSolutionGerm (j : UpperHalfPlane → ℂ) (C : ℂ → ℂ)
    (z : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ τ : ℂ → UpperHalfPlane,
    (fun w ↦ (τ w : ℂ)) =ᶠ[𝓝 z] f ∧
      (fun w ↦ j (τ w)) =ᶠ[𝓝 z] C

namespace IsUpperHalfPlaneSolutionGerm

variable {j : UpperHalfPlane → ℂ} {C f g : ℂ → ℂ} {z : ℂ}

/-- The solution property depends only on the germ of the continued function. -/
theorem congr (hfg : f =ᶠ[𝓝 z] g) (hf : IsUpperHalfPlaneSolutionGerm j C z f) :
    IsUpperHalfPlaneSolutionGerm j C z g := by
  obtain ⟨τ, hτf, hjτ⟩ := hf
  exact ⟨τ, hτf.trans hfg, hjτ⟩

end IsUpperHalfPlaneSolutionGerm

/-- Relation-preserving global branch theorem specialized to upper-half-plane-valued solutions.
The output is first constructed as a complex-valued analytic function; its preserved local germs
canonically prove that it lands in the upper half-plane and satisfies the equation everywhere. -/
theorem ContinuesInsideWith.exists_upperHalfPlane_solution
    {j : UpperHalfPlane → ℂ} {C f₀ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hz₀ : z₀ ∈ U)
    (H : ContinuesInsideWith f₀ U z₀ (IsUpperHalfPlaneSolutionGerm j C)) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F U ∧ F =ᶠ[𝓝 z₀] f₀ ∧
        ∃ hF : ∀ z, z ∈ U → 0 < (F z).im,
          ∀ z (hz : z ∈ U), j ⟨F z, hF z hz⟩ = C z := by
  obtain ⟨F, hFan, hF₀, hFP⟩ :=
    H.exists_analyticOnNhd_and_forall hUo hUc hz₀
      (fun z _ _ hfg hf ↦ hf.congr hfg)
  have hFim : ∀ z, z ∈ U → 0 < (F z).im := by
    intro z hz
    obtain ⟨τ, hτF, -⟩ := hFP z hz
    have hτz : (τ z : ℂ) = F z := hτF.self_of_nhds
    rw [← hτz]
    exact (τ z).im_pos
  refine ⟨F, hFan, hF₀, hFim, fun z hz ↦ ?_⟩
  obtain ⟨τ, hτF, hjτ⟩ := hFP z hz
  have hτz : (τ z : ℂ) = F z := hτF.self_of_nhds
  have hsub : τ z = ⟨F z, hFim z hz⟩ := UpperHalfPlane.coe_injective hτz
  rw [← hsub]
  exact hjτ.self_of_nhds

/-- The upper half-plane, viewed as its standard open subset of `ℂ`, is simply connected. -/
theorem UpperHalfPlane.isSimplyConnected_upperHalfPlaneSet :
    IsSimplyConnected UpperHalfPlane.upperHalfPlaneSet := by
  letI : ContractibleSpace UpperHalfPlane.upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).contractibleSpace ⟨Complex.I, by simp⟩
  change SimplyConnectedSpace UpperHalfPlane.upperHalfPlaneSet
  exact inferInstance

/-- The relation-preserving Tau Ceti monodromy theorem in the exact source/target shape needed
for an upper-half-plane lift.  The only nonlocal input left is `H`: a chosen local solution germ
continued, while preserving the equation, along every source path. -/
theorem ContinuesInsideWith.exists_mdifferentiable_upperHalfPlane_lift
    {j C : UpperHalfPlane → ℂ} {f₀ : ℂ → ℂ} {z₀ : UpperHalfPlane}
    (H : ContinuesInsideWith f₀ UpperHalfPlane.upperHalfPlaneSet (z₀ : ℂ)
      (IsUpperHalfPlaneSolutionGerm j (C ∘ UpperHalfPlane.ofComplex))) :
    ∃ τ : UpperHalfPlane → UpperHalfPlane,
      MDiff τ ∧ (∀ z, j (τ z) = C z) ∧
        (fun w : ℂ ↦ (τ (UpperHalfPlane.ofComplex w) : ℂ)) =ᶠ[𝓝 (z₀ : ℂ)] f₀ := by
  obtain ⟨F, hFan, hF₀, hFim, hFj⟩ :=
    H.exists_upperHalfPlane_solution UpperHalfPlane.isOpen_upperHalfPlaneSet
      UpperHalfPlane.isSimplyConnected_upperHalfPlaneSet z₀.im_pos
  let τ : UpperHalfPlane → UpperHalfPlane := fun z ↦ UpperHalfPlane.ofComplex (F z)
  have hτdiff : MDiff τ := by
    intro z
    have hFdiff : DifferentiableAt ℂ F (z : ℂ) :=
      (hFan (z : ℂ) z.im_pos).differentiableAt
    have hFcomp : MDiffAt (fun w : UpperHalfPlane ↦ F (w : ℂ)) z :=
      hFdiff.mdifferentiableAt.comp z UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt
    exact (UpperHalfPlane.mdifferentiableAt_ofComplex (hFim (z : ℂ) z.im_pos)).comp z hFcomp
  refine ⟨τ, hτdiff, fun z ↦ ?_, ?_⟩
  · have hτz : τ z = ⟨F z, hFim (z : ℂ) z.im_pos⟩ := by
      exact UpperHalfPlane.ofComplex_apply_of_im_pos (hFim (z : ℂ) z.im_pos)
    rw [hτz, hFj (z : ℂ) z.im_pos]
    exact congrArg C (UpperHalfPlane.ofComplex_apply z)
  · apply Filter.EventuallyEq.trans _ hF₀
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z₀.im_pos] with w hw
    have hwcoe : (UpperHalfPlane.ofComplex w : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    have hFw : 0 < (F w).im := hFim w hw
    change (UpperHalfPlane.ofComplex (F (UpperHalfPlane.ofComplex w)) : ℂ) = F w
    rw [hwcoe, UpperHalfPlane.ofComplex_apply_of_im_pos hFw]


end TauCeti
