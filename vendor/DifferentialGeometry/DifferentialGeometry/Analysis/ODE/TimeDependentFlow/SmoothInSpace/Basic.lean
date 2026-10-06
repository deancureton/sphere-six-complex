module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.Selection
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ChartGlue
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

@[expose] public section

namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_flow_smooth_in_space
    (T : ℝ) (hT : 0 < T) (Φ : ℝ → M → M)
    (hLocal : ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
      ContDiffOn ℝ ∞ (Function.uncurry flow)
        (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
        I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
        Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target)) :
    ∀ t : ℝ, 0 < t → t < T → ContMDiff I I ∞ (Φ t) := by
  intro t ht_pos ht_lt
  apply chart_glue_smooth_of_chart_local_smooth
  intro x
  obtain ⟨ρ, hρ_pos, flow, hflow_smooth, hΦ_eq, hflow_target⟩ := hLocal x
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht_pos, ht_lt⟩
  exact manifold_contMDiffAt_of_chart_smooth_flow
    (α := x) (T := T) (hT := hT) (r' := ρ) (hr' := hρ_pos)
    (flow := flow) (ρ := ρ) (hρ := hρ_pos) (hρ_le := le_refl ρ)
    (hflow_smooth := hflow_smooth) (Φ := Φ) (hΦ_eq := hΦ_eq)
    (ht := ht_mem)
    (hx_source := mem_chart_source H x)
    (hx_ball := Metric.mem_ball_self hρ_pos)
    (hflow_in_target := hflow_target t ht_mem)

end DifferentialGeometry.Analysis.ODE
