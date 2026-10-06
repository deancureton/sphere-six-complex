module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineSubdivision

@[expose] public section

/-! # The actual barycenter diameter estimate used by subdivision -/

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Difference from the actual barycenter is the average of the original
differences, including degenerate and zero-dimensional simplices. -/
theorem affineSimplexBarycenter_sub (n : ℕ) (v : Fin (n + 1) → E) (x : E) :
    affineSimplexBarycenter n v - x = ((n + 1 : ℝ)⁻¹) • ∑ i, (v i - x) := by
  have hs : (∑ _i : Fin (n + 1), x) = (n + 1 : ℝ) • x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.cast_smul_eq_nsmul ℝ (n + 1) x).symm
  change (∑ i : Fin (n + 1), Convexity.StdSimplex.barycenter.weights i • v i) - x = _
  simp only [Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, hs, smul_sub, smul_smul,
    inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_smul]

omit [NormedSpace ℝ E] in
/-- The sum of distances from one original vertex is bounded by n times
the original vertex diameter, since its own summand is exactly zero. -/
theorem affineSimplex_vertex_distance_sum (n : ℕ) (v : Fin (n + 1) → E) (j : Fin (n + 1)) :
    (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * Metric.diam (range v) := by
  rw [Fin.sum_univ_succAbove _ j]
  simp only [sub_self, norm_zero, zero_add]
  calc
    (∑ i : Fin n, ‖v (j.succAbove i) - v j‖) ≤ ∑ _i : Fin n, Metric.diam (range v) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem (finite_range v).isBounded ⟨j.succAbove i, rfl⟩ ⟨j, rfl⟩
    _ = (n : ℝ) * Metric.diam (range v) := by simp

/-- The barycenter is at most n/(n+1) times the original diameter from
each original vertex. -/
theorem affineSimplexBarycenter_dist_vertex (n : ℕ) (v : Fin (n + 1) → E) (j : Fin (n + 1)) :
    dist (affineSimplexBarycenter n v) (v j) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (range v) := by
  rw [dist_eq_norm, affineSimplexBarycenter_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)⁻¹)]
  calc
    (n + 1 : ℝ)⁻¹ * ‖∑ i, (v i - v j)‖ ≤
        (n + 1 : ℝ)⁻¹ * ((n : ℝ) * Metric.diam (range v)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (affineSimplex_vertex_distance_sum n v j))
        (by positivity)
    _ = _ := by ring

/-- The same sharp bound holds throughout the entire original convex hull. -/
theorem affineSimplexBarycenter_dist_convexHull (n : ℕ) (v : Fin (n + 1) → E)
    {x : E} (hx : x ∈ convexHull ℝ (range v)) :
    dist (affineSimplexBarycenter n v) x ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (range v) := by
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx (affineSimplexBarycenter n v)
  rw [dist_comm x, dist_comm (v j)] at hj
  exact hj.trans (affineSimplexBarycenter_dist_vertex n v j)

end DifferentialGeometry.Topology
