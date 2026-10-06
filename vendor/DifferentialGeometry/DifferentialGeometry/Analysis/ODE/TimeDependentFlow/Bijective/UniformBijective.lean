module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Bijective.ChartCoverBijective

@[expose] public section

namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem compact_uniform_horizon_extraction
    (U : M → Set M) (S : M → ℝ) (P : ℝ → M → Prop)
    (hU_open : ∀ α : M, IsOpen (U α))
    (hU_mem : ∀ α : M, α ∈ U α)
    (hS_pos : ∀ α : M, 0 < S α)
    (hP : ∀ α : M, ∀ x ∈ U α, ∀ s ∈ Set.Ico (0 : ℝ) (S α), P s x) :
    ∃ T : ℝ, 0 < T ∧ ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, P s x := by
  have hCover : (Set.univ : Set M) ⊆ ⋃ α : M, U α := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨Sfin, hSfin⟩ :=
    isCompact_univ.elim_finite_subcover U hU_open hCover
  rcases Sfin.eq_empty_or_nonempty with hSempty | hSnonempty
  · refine ⟨1, one_pos, ?_⟩
    intro s _ x
    have : x ∈ ⋃ α ∈ Sfin, U α := hSfin (Set.mem_univ x)
    rw [hSempty] at this
    simp at this
  · let Tmin : ℝ := Sfin.image S |>.min' (by
      rw [Finset.image_nonempty]; exact hSnonempty)
    have hTmin_pos : 0 < Tmin := by
      have hmem : Tmin ∈ Sfin.image S := Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmem with ⟨α₀, _, hα₀_eq⟩
      rw [← hα₀_eq]; exact hS_pos α₀
    have hTmin_le : ∀ α ∈ Sfin, Tmin ≤ S α := by
      intro α hα
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
    refine ⟨Tmin, hTmin_pos, ?_⟩
    intro s hs x
    have hx_cover : x ∈ ⋃ α ∈ Sfin, U α := hSfin (Set.mem_univ x)
    rcases Set.mem_iUnion₂.mp hx_cover with ⟨α, hαS, hxU⟩
    have hs_α : s ∈ Set.Ico (0 : ℝ) (S α) :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (hTmin_le α hαS)⟩
    exact hP α x hxU s hs_α

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem chart_cover_flow_bijective_two_sided_uniform_horizon
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (Φ Ψ : ℝ → M → M)
    (hBijPerChart : ∀ α : M,
      ∃ S_α : ℝ, 0 < S_α ∧
        ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
          ∀ s ∈ Set.Ico (0 : ℝ) S_α,
            Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ T : ℝ, 0 < T ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) := by
  classical
  have hExtracted := compact_uniform_horizon_extraction
    (fun α => (hper α).U ∩ (hperNeg α).U)
    (fun α => (hBijPerChart α).choose)
    (fun s x => Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x)
    (fun α => (hper α).isOpen_U.inter (hperNeg α).isOpen_U)
    (fun α => ⟨(hper α).mem_U_self, (hperNeg α).mem_U_self⟩)
    (fun α => (hBijPerChart α).choose_spec.1)
    (fun α x hx s hs => (hBijPerChart α).choose_spec.2 x hx s hs)
  obtain ⟨T, hT_pos, hT_bij⟩ := hExtracted
  exact ⟨T, hT_pos, fun s hs x => (hT_bij s hs x).1, fun s hs x => (hT_bij s hs x).2⟩

end DifferentialGeometry.Analysis.ODE
