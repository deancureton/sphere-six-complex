module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.UniformExistence
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem chart_local_picard_flow_selection
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ S : Finset M, (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) ∧
        ∃ Φ : ℝ → M → M,
          (∀ x : M, Φ 0 x = x) ∧
          ∀ x : M, ∃ α ∈ S, x ∈ (hper α).U ∧
            T ≤ (hper α).T ∧
            ∀ s : ℝ,
              Φ s x = (chartAt H α).symm
                (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := by
  obtain ⟨T, hT_pos, S, hCoverEq, hTle⟩ :=
    chart_local_picard_uniform_time X hper
  have hMem : ∀ x : M, ∃ α ∈ S, x ∈ (hper α).U := by
    intro x
    have hx : x ∈ (⋃ α ∈ S, (hper α).U) := by
      rw [hCoverEq]; exact Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨α, hαS, hxU⟩
    exact ⟨α, hαS, hxU⟩
  classical
  let αRep : M → M := fun x => (hMem x).choose
  have hαRep_S : ∀ x : M, αRep x ∈ S := fun x => (hMem x).choose_spec.1
  have hαRep_U : ∀ x : M, x ∈ (hper (αRep x)).U :=
    fun x => (hMem x).choose_spec.2
  have hxChart_closedBall :
      ∀ x : M, I ((chartAt H (αRep x)) x) ∈
        Metric.closedBall (I ((chartAt H (αRep x)) (αRep x))) (hper (αRep x)).r := by
    intro x
    have hxU := hαRep_U x
    have hball : I ((chartAt H (αRep x)) x) ∈
        Metric.ball (I ((chartAt H (αRep x)) (αRep x))) (hper (αRep x)).r := by
      have : (chartAt H (αRep x)) x ∈
          I ⁻¹' Metric.ball (I ((chartAt H (αRep x)) (αRep x))) (hper (αRep x)).r := by
        unfold ChartLocalPicardData.U at hxU
        exact hxU.2
      exact this
    exact Metric.ball_subset_closedBall hball
  have hxChart_source : ∀ x : M, x ∈ (chartAt H (αRep x)).source := by
    intro x
    have hxU := hαRep_U x
    unfold ChartLocalPicardData.U at hxU
    exact hxU.1
  let Φ : ℝ → M → M := fun s x =>
    (chartAt H (αRep x)).symm
      (I.symm ((hper (αRep x)).flow (I ((chartAt H (αRep x)) x)) s))
  have hΦ_initial : ∀ x : M, Φ 0 x = x := by
    intro x
    obtain ⟨hinit, _⟩ :=
      (hper (αRep x)).flow_spec (I ((chartAt H (αRep x)) x)) (hxChart_closedBall x)
    change (chartAt H (αRep x)).symm
        (I.symm ((hper (αRep x)).flow (I ((chartAt H (αRep x)) x)) 0)) = x
    rw [hinit]
    have hI_left : I.symm (I ((chartAt H (αRep x)) x)) = (chartAt H (αRep x)) x :=
      I.left_inv ((chartAt H (αRep x)) x)
    rw [hI_left]
    exact (chartAt H (αRep x)).left_inv (hxChart_source x)
  refine ⟨T, hT_pos, S, hCoverEq, Φ, hΦ_initial, ?_⟩
  intro x
  refine ⟨αRep x, hαRep_S x, hαRep_U x, hTle (αRep x) (hαRep_S x), ?_⟩
  intro s
  rfl

end DifferentialGeometry.Analysis.ODE
