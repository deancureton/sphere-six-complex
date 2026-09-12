module

public import SphereSixComplex.Prerequisites.Topology.ConstructedCircleCell

@[expose] public section
noncomputable section
open Set

namespace SphereSixComplex.SupNormBall

public theorem append_mem_closedBall_iff (m n : ℕ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    Fin.append x.1 x.2 ∈ Metric.closedBall 0 1 ↔
      x ∈ (Metric.closedBall (0 : Fin m → ℝ) 1) ×ˢ
        (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  simp [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Fin.forall_fin_add]

public theorem split_mem_closedBall_iff (m n : ℕ) (x : Fin (m + n) → ℝ) :
    x ∈ Metric.closedBall 0 1 ↔
      (Fin.appendHomeomorph (X := ℝ) m n).symm x ∈
        (Metric.closedBall (0 : Fin m → ℝ) 1) ×ˢ
          (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  have h := append_mem_closedBall_iff m n ((Fin.appendHomeomorph (X := ℝ) m n).symm x)
  change (Fin.appendHomeomorph (X := ℝ) m n) ((Fin.appendHomeomorph (X := ℝ) m n).symm x) ∈
    Metric.closedBall 0 1 ↔ _ at h
  rw [(Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply] at h
  exact h

public theorem split_mem_ball_iff (m n : ℕ) (x : Fin (m + n) → ℝ) :
    x ∈ Metric.ball 0 1 ↔
      (Fin.appendHomeomorph (X := ℝ) m n).symm x ∈
        (Metric.ball (0 : Fin m → ℝ) 1) ×ˢ (Metric.ball (0 : Fin n → ℝ) 1) := by
  have h := SupNormBall.append_mem_ball_iff m n ((Fin.appendHomeomorph (X := ℝ) m n).symm x)
  change (Fin.appendHomeomorph (X := ℝ) m n) ((Fin.appendHomeomorph (X := ℝ) m n).symm x) ∈
    Metric.ball 0 1 ↔ _ at h
  rw [(Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply] at h
  exact h

public theorem split_mem_sphere (m n : ℕ) (x : Fin (m + n) → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    ((Fin.appendHomeomorph (X := ℝ) m n).symm x).1 ∈ Metric.sphere 0 1 ∨
      ((Fin.appendHomeomorph (X := ℝ) m n).symm x).2 ∈ Metric.sphere 0 1 := by
  have hc := (split_mem_closedBall_iff m n x).mp (Metric.sphere_subset_closedBall hx)
  have hb : x ∉ Metric.ball 0 1 := Set.disjoint_left.mp Metric.sphere_disjoint_ball hx
  by_cases hleft : ((Fin.appendHomeomorph (X := ℝ) m n).symm x).1 ∈ Metric.ball 0 1
  · apply Or.inr
    rw [← Metric.closedBall_sdiff_ball]
    refine ⟨hc.2, ?_⟩
    intro hright
    exact hb ((split_mem_ball_iff m n x).mpr ⟨hleft, hright⟩)
  · apply Or.inl
    rw [← Metric.closedBall_sdiff_ball]
    exact ⟨hc.1, hleft⟩

end SphereSixComplex.SupNormBall
