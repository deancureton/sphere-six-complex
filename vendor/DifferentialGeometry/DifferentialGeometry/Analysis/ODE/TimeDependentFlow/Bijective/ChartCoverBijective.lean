module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.Selection
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem portPrivate_1c7c5453_chart_pullback_to_manifold_eq_via_chart_coord_inv
    (α : M) (cflow : ℝ → E) (t : ℝ) (x q : M)
    (hx_source : x ∈ (chartAt H α).source)
    (hq_repr : q = (chartAt H α).symm (I.symm (cflow t)))
    (hChartCoord_eq : cflow t = I ((chartAt H α) x)) :
    q = x := by
  rw [hq_repr, hChartCoord_eq, I.left_inv]
  exact (chartAt H α).left_inv hx_source

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem portPrivate_1c7c5453_chart_cover_flow_bijective_single_chart_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hperNeg : ChartLocalPicardData (fun t x => -(X t x)) α)
    (Ψ : ℝ → M → M) (Φtx : M) (t : ℝ)
    (x : M) (hx_source : x ∈ (chartAt H α).source)
    (hΨ_repr_at_Φt : Ψ t Φtx = (chartAt H α).symm
      (I.symm ((hperNeg).flow (I ((chartAt H α) Φtx)) t)))
    (hChartCoord_inv :
      (hperNeg).flow (I ((chartAt H α) Φtx)) t = I ((chartAt H α) x)) :
    Ψ t Φtx = x := by
  exact portPrivate_1c7c5453_chart_pullback_to_manifold_eq_via_chart_coord_inv
    (α := α)
    (cflow := fun s => (hperNeg).flow (I ((chartAt H α) Φtx)) s)
    (t := t) (x := x) (q := Ψ t Φtx)
    hx_source hΨ_repr_at_Φt hChartCoord_inv

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem chart_cover_flow_bijective_on_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (Φ Ψ : ℝ → M → M) (T : ℝ)
    (hPick : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Ψ s (Φ s x) = (chartAt H α_x).symm
            (I.symm ((hperNeg α_x).flow
              (I ((chartAt H α_x) (Φ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hperNeg α_x).flow
            (I ((chartAt H α_x) (Φ s x))) s
            = I ((chartAt H α_x) x))) :
    ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∀ s ∈ Set.Ico (0 : ℝ) S, Ψ s (Φ s x) = x := by
  classical
  intro x
  obtain ⟨S, hS_pos, hS_le, α_x, hx_source, hΨ_repr_at_Φ, hChartCoord_inv⟩ :=
    hPick x
  refine ⟨S, hS_pos, hS_le, ?_⟩
  intro s hs
  exact portPrivate_1c7c5453_chart_cover_flow_bijective_single_chart_short_time
    (X := X) (α := α_x) (hperNeg := hperNeg α_x)
    (Ψ := Ψ) (Φtx := Φ s x) (t := s)
    (x := x) (hx_source := hx_source)
    (hΨ_repr_at_Φ s hs) (hChartCoord_inv s hs)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem chart_cover_flow_bijective_on_short_time_symm
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (Φ Ψ : ℝ → M → M) (T : ℝ)
    (hPick : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Φ s (Ψ s x) = (chartAt H α_x).symm
            (I.symm ((hper α_x).flow
              (I ((chartAt H α_x) (Ψ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hper α_x).flow
            (I ((chartAt H α_x) (Ψ s x))) s
            = I ((chartAt H α_x) x))) :
    ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∀ s ∈ Set.Ico (0 : ℝ) S, Φ s (Ψ s x) = x := by
  classical
  intro x
  obtain ⟨S, hS_pos, hS_le, α_x, hx_source, hΦ_repr_at_Ψ, hChartCoord_inv⟩ :=
    hPick x
  refine ⟨S, hS_pos, hS_le, ?_⟩
  intro s hs
  exact portPrivate_1c7c5453_chart_pullback_to_manifold_eq_via_chart_coord_inv
    (α := α_x)
    (cflow := fun u => (hper α_x).flow (I ((chartAt H α_x) (Ψ s x))) u)
    (t := s) (x := x) (q := Φ s (Ψ s x))
    hx_source (hΦ_repr_at_Ψ s hs) (hChartCoord_inv s hs)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem chart_cover_flow_bijective_two_sided_on_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (Φ Ψ : ℝ → M → M) (T : ℝ)
    (hPickFwd : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Ψ s (Φ s x) = (chartAt H α_x).symm
            (I.symm ((hperNeg α_x).flow
              (I ((chartAt H α_x) (Φ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hperNeg α_x).flow
            (I ((chartAt H α_x) (Φ s x))) s
            = I ((chartAt H α_x) x)))
    (hPickRev : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Φ s (Ψ s x) = (chartAt H α_x).symm
            (I.symm ((hper α_x).flow
              (I ((chartAt H α_x) (Ψ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hper α_x).flow
            (I ((chartAt H α_x) (Ψ s x))) s
            = I ((chartAt H α_x) x))) :
    ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∀ s ∈ Set.Ico (0 : ℝ) S,
        Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x := by
  classical
  intro x
  obtain ⟨S₁, hS₁_pos, hS₁_le, hBij_fwd⟩ :=
    chart_cover_flow_bijective_on_short_time
      (M := M) (I := I) (E := E)
      X hperNeg Φ Ψ T hPickFwd x
  obtain ⟨S₂, hS₂_pos, hS₂_le, hBij_rev⟩ :=
    chart_cover_flow_bijective_on_short_time_symm
      (M := M) (I := I) (E := E)
      X hper Φ Ψ T hPickRev x
  refine ⟨min S₁ S₂, lt_min hS₁_pos hS₂_pos,
    (min_le_left _ _).trans hS₁_le, ?_⟩
  intro s hs
  have hs_S₁ : s ∈ Set.Ico (0 : ℝ) S₁ :=
    ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hs_S₂ : s ∈ Set.Ico (0 : ℝ) S₂ :=
    ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
  exact ⟨hBij_fwd s hs_S₁, hBij_rev s hs_S₂⟩

end DifferentialGeometry.Analysis.ODE
