module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Bundle IsManifold
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem chart_glue_smooth_of_chart_local_smooth
    (f : M → M)
    (h : ∀ x : M, ContMDiffAt I I ∞ f x) :
    ContMDiff I I ∞ f := h

theorem chart_cover_stitch_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → M)
    (h : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ContMDiffAt I I ∞ f y) :
    ContMDiff I I ∞ f := by
  intro x
  obtain ⟨U, _hUopen, hxU, hU⟩ := h x
  exact hU x hxU

theorem manifold_contMDiffAt_of_chart_smooth_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [I.Boundaryless]
    (α : M) (T : ℝ) (hT : 0 < T) (r' : ℝ) (hr' : 0 < r')
    (flow : E → ℝ → E)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ_le : ρ ≤ r')
    (hflow_smooth : ContDiffOn ℝ ∞ (Function.uncurry flow)
      ((Metric.ball (I ((chartAt H α) α)) ρ) ×ˢ Set.Ioo (0 : ℝ) T))
    (Φ : ℝ → M → M)
    (hΦ_eq : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ (chartAt H α).source,
      I ((chartAt H α) x) ∈ Metric.ball (I ((chartAt H α) α)) ρ →
      Φ s x = (chartAt H α).symm
        (I.symm (flow (I ((chartAt H α) x)) s)))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {x : M} (hx_source : x ∈ (chartAt H α).source)
    (hx_ball : I ((chartAt H α) x) ∈
      Metric.ball (I ((chartAt H α) α)) ρ)
    (hflow_in_target :
      I.symm (flow (I ((chartAt H α) x)) t) ∈ (chartAt H α).target) :
    ContMDiffAt I I ∞ (Φ t) x := by
  have _hT := hT
  have _hr' := hr'
  have _hρ := hρ
  have _hρ_le := hρ_le
  let Ψ : M → M := fun y => (chartAt H α).symm
    (I.symm (flow (I ((chartAt H α) y)) t))
  let U : Set M := (chartAt H α).source ∩
    (fun y : M => I ((chartAt H α) y)) ⁻¹'
      Metric.ball (I ((chartAt H α) α)) ρ
  have hUopen : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_
      (chartAt H α).open_source Metric.isOpen_ball
    exact I.continuous.comp_continuousOn (chartAt H α).continuousOn
  have hxU : x ∈ U := ⟨hx_source, hx_ball⟩
  have hUnhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  have hEqOn : Set.EqOn (Φ t) Ψ U := by
    intro y hy
    obtain ⟨hy_source, hy_ball⟩ := hy
    exact hΦ_eq t ht y hy_source hy_ball
  have hEqEv : Φ t =ᶠ[𝓝 x] Ψ := Filter.eventuallyEq_of_mem hUnhds hEqOn
  have h_chart : ContMDiffAt I I ∞ (chartAt H α) x :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas α) hx_source
  have h_I : ContMDiffAt I 𝓘(ℝ, E) ∞ I ((chartAt H α) x) :=
    I.contMDiff.contMDiffAt
  have h_I_chart : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y : M => I ((chartAt H α) y)) x :=
    h_I.comp x h_chart
  have h_flow_y : ContDiffAt ℝ ∞ (fun y : E => flow y t)
      (I ((chartAt H α) x)) := by
    have hmem : ((I ((chartAt H α) x), t) : E × ℝ) ∈
        (Metric.ball (I ((chartAt H α) α)) ρ) ×ˢ Set.Ioo (0 : ℝ) T :=
      ⟨hx_ball, ht⟩
    have hSopen : IsOpen
        ((Metric.ball (I ((chartAt H α) α)) ρ) ×ˢ Set.Ioo (0 : ℝ) T) :=
      Metric.isOpen_ball.prod isOpen_Ioo
    have h_uncurry_at : ContDiffAt ℝ ∞ (Function.uncurry flow)
        (I ((chartAt H α) x), t) :=
      hflow_smooth.contDiffAt (hSopen.mem_nhds hmem)
    have h_mk : ContDiffAt ℝ ∞ (fun y : E => (y, t))
        (I ((chartAt H α) x)) :=
      (contDiff_prodMk_left t).contDiffAt
    have h_comp : ContDiffAt ℝ ∞
        ((Function.uncurry flow) ∘ (fun y : E => (y, t)))
        (I ((chartAt H α) x)) :=
      ContDiffAt.comp (I ((chartAt H α) x)) h_uncurry_at h_mk
    exact h_comp
  have h_flow_y_M : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : E => flow y t)
      (I ((chartAt H α) x)) := h_flow_y.contMDiffAt
  have h_I_symm : ContMDiff 𝓘(ℝ, E) I ∞ (I.symm : E → H) := by
    rw [← contMDiffOn_univ, ← I.range_eq_univ]
    exact I.contMDiffOn_symm
  have h_chart_symm : ContMDiffAt I I ∞ (chartAt H α).symm
      (I.symm (flow (I ((chartAt H α) x)) t)) :=
    (contMDiffOn_chart_symm (I := I) (x := α)).contMDiffAt
      ((chartAt H α).open_target.mem_nhds hflow_in_target)
  have h_step1 : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y : M => flow (I ((chartAt H α) y)) t) x :=
    h_flow_y_M.comp x h_I_chart
  have h_step2 : ContMDiffAt I I ∞
      (fun y : M => I.symm (flow (I ((chartAt H α) y)) t)) x :=
    h_I_symm.contMDiffAt.comp x h_step1
  have hΨ_smooth : ContMDiffAt I I ∞ Ψ x := h_chart_symm.comp x h_step2
  exact hΨ_smooth.congr_of_eventuallyEq hEqEv

end DifferentialGeometry.Analysis.ODE
