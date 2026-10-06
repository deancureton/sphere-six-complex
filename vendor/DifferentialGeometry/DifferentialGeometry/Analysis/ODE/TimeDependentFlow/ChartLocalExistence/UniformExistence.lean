module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

structure ChartLocalPicardData
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) where
  T : ℝ
  T_pos : 0 < T
  r : ℝ
  r_pos : 0 < r
  flow : E → ℝ → E
  flow_spec : ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r,
    flow y 0 = y ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (flow y)
        ((X t ((chartAt H α).symm (I.symm (flow y t)))) : E)
        (Set.Icc (0 : ℝ) T) t

def ChartLocalPicardData.U
    {X : ℝ → ∀ x : M, TangentSpace I x} {α : M}
    (data : ChartLocalPicardData X α) : Set M :=
  (chartAt H α).source ∩
    ((chartAt H α) ⁻¹' (I ⁻¹' Metric.ball (I ((chartAt H α) α)) data.r))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma ChartLocalPicardData.isOpen_U
    {X : ℝ → ∀ x : M, TangentSpace I x} {α : M}
    (data : ChartLocalPicardData X α) : IsOpen data.U := by
  unfold ChartLocalPicardData.U
  have h₁ : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have h₂ : IsOpen (I ⁻¹' Metric.ball (I ((chartAt H α) α)) data.r) :=
    Metric.isOpen_ball.preimage I.continuous_toFun
  have h₃ : ContinuousOn (chartAt H α) (chartAt H α).source :=
    (chartAt H α).continuousOn
  exact h₃.isOpen_inter_preimage h₁ h₂

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma ChartLocalPicardData.mem_U_self
    {X : ℝ → ∀ x : M, TangentSpace I x} {α : M}
    (data : ChartLocalPicardData X α) : α ∈ data.U := by
  unfold ChartLocalPicardData.U
  refine ⟨mem_chart_source H α, ?_⟩
  exact Metric.mem_ball_self data.r_pos

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem chart_local_picard_uniform_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ S : Finset M, (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) ∧
        ∀ α ∈ S, T ≤ (hper α).T := by
  have hCompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hOpenU : ∀ α : M, IsOpen ((hper α).U) := fun α => (hper α).isOpen_U
  have hCover : (Set.univ : Set M) ⊆ ⋃ α : M, (hper α).U := by
    intro x _
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    exact (hper x).mem_U_self
  obtain ⟨S, hS⟩ :=
    hCompact.elim_finite_subcover (fun α : M => (hper α).U) hOpenU hCover
  have hCoverEq : (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) := by
    apply Set.eq_univ_of_univ_subset
    exact hS
  rcases Finset.eq_empty_or_nonempty S with hSempty | hSnonempty
  · refine ⟨1, by norm_num, S, hCoverEq, ?_⟩
    intro α hα
    rw [hSempty] at hα
    exact absurd hα (Finset.notMem_empty α)
  · let Tmin : ℝ := S.image (fun α : M => (hper α).T) |>.min' (by
      rw [Finset.image_nonempty]; exact hSnonempty)
    have hTmin_pos : 0 < Tmin := by
      have hmem : Tmin ∈ S.image (fun α : M => (hper α).T) :=
        Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmem with ⟨α₀, _, hα₀_eq⟩
      rw [← hα₀_eq]
      exact (hper α₀).T_pos
    have hTmin_le : ∀ α ∈ S, Tmin ≤ (hper α).T := by
      intro α hα
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
    exact ⟨Tmin, hTmin_pos, S, hCoverEq, hTmin_le⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem chart_local_picard_uniform_flow
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ S : Finset M, (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) ∧
        ∃ flow : M → E → ℝ → E,
          ∀ α ∈ S,
            ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) (hper α).r,
              flow α y 0 = y ∧
              ∀ t ∈ Set.Icc (0 : ℝ) T,
                HasDerivWithinAt (flow α y)
                  ((X t ((chartAt H α).symm (I.symm (flow α y t)))) : E)
                  (Set.Icc (0 : ℝ) T) t := by
  obtain ⟨T, hT, S, hCover, hTle⟩ := chart_local_picard_uniform_time X hper
  refine ⟨T, hT, S, hCover, fun α => (hper α).flow, ?_⟩
  intro α hα y hy
  obtain ⟨hinit, hflow⟩ := (hper α).flow_spec y hy
  refine ⟨hinit, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) (hper α).T :=
    ⟨ht.1, ht.2.trans (hTle α hα)⟩
  have hderiv := hflow t ht'
  have hsub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) (hper α).T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans (hTle α hα)⟩
  exact hderiv.mono hsub

end DifferentialGeometry.Analysis.ODE
