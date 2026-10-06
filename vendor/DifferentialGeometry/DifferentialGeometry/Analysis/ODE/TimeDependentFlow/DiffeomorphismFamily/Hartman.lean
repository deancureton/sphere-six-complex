module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.Selection
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.Basic
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Bijective.UniformBijective

@[expose] public section


open scoped Manifold Topology ContDiff

theorem time_dependent_vf_globalflow_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {T : ℝ}
    {Φ Ψ : ℝ → M → M}
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∀ t, 0 < t → t < T →
      ∃ d : Diffeomorph I I M M ∞,
        (∀ x, d x = Φ t x) ∧ (∀ x, d.symm x = Ψ t x) := by
  intro t ht htT
  have hmem : t ∈ Set.Ico (0 : ℝ) T := Set.mem_Ico.mpr ⟨le_of_lt ht, htT⟩
  let e : M ≃ M :=
    { toFun := Φ t
      invFun := Ψ t
      left_inv := fun x => hΨΦ t hmem x
      right_inv := fun x => hΦΨ t hmem x }
  exact ⟨⟨e, hΦ_smooth t ht htT, hΨ_smooth t ht htT⟩, fun x => rfl, fun x => rfl⟩

namespace DifferentialGeometry.Analysis.ODE

open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ChartLocalPicardData.flow_initial_value
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hper : ChartLocalPicardData X α)
    (x : M) (hx : x ∈ hper.U) :
    (chartAt H α).symm (I.symm (hper.flow (I ((chartAt H α) x)) 0)) = x := by
  have hx_source : x ∈ (chartAt H α).source := by
    unfold ChartLocalPicardData.U at hx; exact hx.1
  have hx_closedBall : I ((chartAt H α) x) ∈
      Metric.closedBall (I ((chartAt H α) α)) hper.r := by
    unfold ChartLocalPicardData.U at hx
    exact Metric.ball_subset_closedBall hx.2
  obtain ⟨hinit, _⟩ := hper.flow_spec (I ((chartAt H α) x)) hx_closedBall
  rw [hinit, I.left_inv]
  exact (chartAt H α).left_inv hx_source

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chart_coord_roundtrip
    (α x : M) (hx : x ∈ (chartAt H α).source) :
    (chartAt H α).symm (I.symm (I ((chartAt H α) x))) = x := by
  rw [I.left_inv]
  exact (chartAt H α).left_inv hx

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ChartLocalPicardData.chart_coord_mem_closedBall
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hper : ChartLocalPicardData X α)
    (x : M) (hx : x ∈ hper.U) :
    I ((chartAt H α) x) ∈ Metric.closedBall (I ((chartAt H α) α)) hper.r := by
  unfold ChartLocalPicardData.U at hx
  exact Metric.ball_subset_closedBall hx.2


omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_flow_diffeomorph_on_closed_manifold
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ (Φ : ℝ → M → M),
        (∀ x, Φ 0 x = x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        ∀ t, 0 < t → t < T →
          ∃ d : Diffeomorph I I M M ∞, ∀ x, d x = Φ t x := by
  obtain ⟨T_fwd, hT_fwd_pos, _S_fwd, _hCover_fwd, Φ, hΦ_initial, hΦ_repr⟩ :=
    chart_local_picard_flow_selection X hper
  have hΦ_repr' : ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
      ∀ s : ℝ, Φ s x = (chartAt H α).symm
        (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := by
    intro x
    obtain ⟨α, _hαS, hxU, _hTle, hrepr⟩ := hΦ_repr x
    exact ⟨α, hxU, hrepr⟩
  have hΦ_repr_simple : ∀ x : M, ∃ α : M, ∀ s : ℝ,
      Φ s x = (chartAt H α).symm
        (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := by
    intro x; obtain ⟨α, _, hrepr⟩ := hΦ_repr' x; exact ⟨α, hrepr⟩
  obtain ⟨T_rev, hT_rev_pos, _S_rev, _hCover_rev, Ψ, hΨ_initial, hΨ_repr⟩ :=
    chart_local_picard_flow_selection (fun t x => -(X t x)) hperNeg
  have hΨ_repr' : ∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
      ∀ s : ℝ, Ψ s x = (chartAt H α).symm
        (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)) := by
    intro x
    obtain ⟨α, _hαS, hxU, _hTle, hrepr⟩ := hΨ_repr x
    exact ⟨α, hxU, hrepr⟩
  have hΨ_repr_simple : ∀ x : M, ∃ α : M, ∀ s : ℝ,
      Ψ s x = (chartAt H α).symm
        (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)) := by
    intro x; obtain ⟨α, _, hrepr⟩ := hΨ_repr' x; exact ⟨α, hrepr⟩
  have hLocalFwd_data := hLocalFwd Φ T_fwd hT_fwd_pos hΦ_repr'
  have hΦ_smooth : ∀ t : ℝ, 0 < t → t < T_fwd → ContMDiff I I ∞ (Φ t) :=
    time_dependent_vf_flow_smooth_in_space T_fwd hT_fwd_pos Φ hLocalFwd_data
  have hLocalRev_data := hLocalRev Ψ T_rev hT_rev_pos hΨ_repr'
  have hΨ_smooth : ∀ t : ℝ, 0 < t → t < T_rev → ContMDiff I I ∞ (Ψ t) :=
    time_dependent_vf_flow_smooth_in_space
      T_rev hT_rev_pos Ψ hLocalRev_data
  have hBij := hBijPerChart Φ Ψ hΦ_initial hΨ_initial hΦ_repr_simple hΨ_repr_simple
  obtain ⟨T_bij, hT_bij_pos, hΨΦ_eq, hΦΨ_eq⟩ :=
    chart_cover_flow_bijective_two_sided_uniform_horizon
      X hper hperNeg Φ Ψ hBij
  set T : ℝ := min (min T_fwd T_rev) T_bij with hT_def
  have hT_pos : 0 < T := lt_min (lt_min hT_fwd_pos hT_rev_pos) hT_bij_pos
  have hΦ_smooth_T : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t) := by
    intro t ht htT
    exact hΦ_smooth t ht (lt_of_lt_of_le htT (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hΨ_smooth_T : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t) := by
    intro t ht htT
    exact hΨ_smooth t ht (lt_of_lt_of_le htT (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x := by
    intro s hs x
    exact hΨΦ_eq s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩ x
  have hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x := by
    intro s hs x
    exact hΦΨ_eq s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩ x
  have hDiffeo := time_dependent_vf_globalflow_diffeomorph
    (I := I) hΦ_smooth_T hΨ_smooth_T hΨΦ hΦΨ
  refine ⟨T, hT_pos, Φ, hΦ_initial, hΦ_repr_simple, ?_⟩
  intro t ht htT
  obtain ⟨d, hd_fwd, _⟩ := hDiffeo t ht htT
  exact ⟨d, hd_fwd⟩

end DifferentialGeometry.Analysis.ODE
