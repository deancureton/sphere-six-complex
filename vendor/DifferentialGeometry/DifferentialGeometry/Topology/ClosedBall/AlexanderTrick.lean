module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

@[expose] public section

namespace DifferentialGeometry.Topology

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped Classical in
noncomputable def coneExtend (h : sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) : E :=
  if hx : x = 0 then 0
  else ‖x‖ • ((h ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx)⟩ :
    sphere (0 : E) 1) : E)

theorem coneExtend_zero (h : sphere (0 : E) 1 → sphere (0 : E) 1) : coneExtend h 0 = 0 := by
  simp [coneExtend]

theorem coneExtend_of_ne_zero (h : sphere (0 : E) 1 → sphere (0 : E) 1) {x : E} (hx : x ≠ 0) :
    coneExtend h x =
      ‖x‖ • ((h ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx)⟩ :
        sphere (0 : E) 1) : E) := by
  simp [coneExtend, hx]

theorem norm_coneExtend (h : sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) :
    ‖coneExtend h x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp [coneExtend_zero]
  · rw [coneExtend_of_ne_zero h hx, norm_smul, Real.norm_of_nonneg (norm_nonneg x),
      mem_sphere_zero_iff_norm.mp (h _).2, mul_one]

theorem coneExtend_apply_sphere (h : sphere (0 : E) 1 → sphere (0 : E) 1) (s : sphere (0 : E) 1) :
    coneExtend h s = h s := by
  have hs : ‖(s : E)‖ = 1 := mem_sphere_zero_iff_norm.mp s.2
  have hne : (s : E) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    exact zero_ne_one hs
  rw [coneExtend_of_ne_zero h hne]
  have : (⟨‖(s : E)‖⁻¹ • (s : E), mem_sphere_zero_iff_norm.mpr
      (norm_smul_inv_norm (𝕜 := ℝ) hne)⟩ : sphere (0 : E) 1) = s := by
    apply Subtype.ext
    simp [hs]
  rw [this, hs, one_smul]

theorem continuous_coneExtend_restrict {h : sphere (0 : E) 1 → sphere (0 : E) 1}
    (hh : Continuous h) : Continuous fun y : {y : E // y ≠ 0} => coneExtend h y := by
  have hg : Continuous fun y : {y : E // y ≠ 0} =>
      (⟨‖(y : E)‖⁻¹ • (y : E), mem_sphere_zero_iff_norm.mpr
        (norm_smul_inv_norm (𝕜 := ℝ) y.2)⟩ : sphere (0 : E) 1) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.norm.inv₀ fun y => norm_ne_zero_iff.mpr y.2).smul
      continuous_subtype_val
  have : (fun y : {y : E // y ≠ 0} => coneExtend h y) = fun y : {y : E // y ≠ 0} =>
      ‖(y : E)‖ • ((h ⟨‖(y : E)‖⁻¹ • (y : E), mem_sphere_zero_iff_norm.mpr
        (norm_smul_inv_norm (𝕜 := ℝ) y.2)⟩ : sphere (0 : E) 1) : E) := by
    funext y
    exact coneExtend_of_ne_zero h y.2
  rw [this]
  exact continuous_subtype_val.norm.smul (continuous_subtype_val.comp (hh.comp hg))

theorem continuous_coneExtend {h : sphere (0 : E) 1 → sphere (0 : E) 1} (hh : Continuous h) :
    Continuous (coneExtend h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, coneExtend_zero, tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, norm_coneExtend]
    simpa using continuous_norm.tendsto (0 : E)
  · have hopen : IsOpen {y : E | y ≠ 0} := isOpen_ne
    have hcont : ContinuousOn (coneExtend h) {y : E | y ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact continuous_coneExtend_restrict hh
    exact hcont.continuousAt (hopen.mem_nhds hx)

theorem coneExtend_coneExtend (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    coneExtend h (coneExtend h.symm x) = x := by
  by_cases hx : x = 0
  · subst hx
    rw [coneExtend_zero, coneExtend_zero]
  · set y := coneExtend h.symm x with hy
    have hny : ‖y‖ = ‖x‖ := norm_coneExtend _ x
    have hyne : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hny
      exact hx (norm_eq_zero.mp hny.symm)
    rw [coneExtend_of_ne_zero h hyne]
    have hpt : (⟨‖y‖⁻¹ • y, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hyne)⟩ :
        sphere (0 : E) 1) =
        h.symm ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx)⟩ := by
      apply Subtype.ext
      simp only
      rw [hny, hy, coneExtend_of_ne_zero h.symm hx, smul_smul,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
    rw [hpt, hny, Homeomorph.apply_symm_apply]
    simp only
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

noncomputable def coneHomeomorph (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) : E ≃ₜ E where
  toFun := coneExtend h
  invFun := coneExtend h.symm
  left_inv x := by
    have := coneExtend_coneExtend h.symm x
    rwa [Homeomorph.symm_symm] at this
  right_inv x := coneExtend_coneExtend h x
  continuous_toFun := continuous_coneExtend h.continuous
  continuous_invFun := continuous_coneExtend h.symm.continuous

theorem coneHomeomorph_apply (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    coneHomeomorph h x = coneExtend h x :=
  rfl

theorem alexander_trick (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    ∃ H : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1,
      ∀ s : sphere (0 : E) 1, H ⟨s, sphere_subset_closedBall s.2⟩ =
        ⟨h s, sphere_subset_closedBall (h s).2⟩ := by
  have hiff : ∀ x : E, x ∈ closedBall (0 : E) 1 ↔ coneHomeomorph h x ∈ closedBall (0 : E) 1 := by
    intro x
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, coneHomeomorph_apply, norm_coneExtend]
  refine ⟨(coneHomeomorph h).subtype hiff, fun s => ?_⟩
  apply Subtype.ext
  rw [Homeomorph.subtype_apply_coe, coneHomeomorph_apply]
  exact coneExtend_apply_sphere h s

end DifferentialGeometry.Topology
