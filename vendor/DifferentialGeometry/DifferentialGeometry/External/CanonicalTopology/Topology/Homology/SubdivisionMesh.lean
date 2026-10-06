module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.MeshBoundary

@[expose] public section

/-! # Geometric mesh shrinking for the original affine subdivision -/

noncomputable section

open CategoryTheory Set Module

universe u

namespace DifferentialGeometry.Topology

/-- The barycentric subdivision factor in dimension n. -/
def affineSubdivisionFactor (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

/-- The factor is nonnegative in every dimension. -/
theorem affineSubdivisionFactor_nonneg (n : ℕ) : 0 ≤ affineSubdivisionFactor n := by
  unfold affineSubdivisionFactor
  positivity

/-- In each fixed finite dimension the factor is strictly below one. -/
theorem affineSubdivisionFactor_lt_one (n : ℕ) : affineSubdivisionFactor n < 1 := by
  unfold affineSubdivisionFactor
  rw [div_lt_one (by positivity)]
  linarith

/-- The face-dimensional factor is no larger than the original factor. -/
theorem affineSubdivisionFactor_le_succ (n : ℕ) :
    affineSubdivisionFactor n ≤ affineSubdivisionFactor (n + 1) := by
  unfold affineSubdivisionFactor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One subdivision reduces the actual mesh by n/(n+1), retaining the
same convex carrier and the same original affine-chain operators. -/
theorem affineSingularSubdivision_mesh (n : ℕ) {A : Set E} (hA : Convex ℝ A) (δ : ℝ)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularMesh n A δ) :
    affineSingularSubdivision n c ∈ affineSingularMesh n A (affineSubdivisionFactor n * δ) := by
  induction n generalizing A δ with
  | zero =>
    change c ∈ affineSingularMesh 0 A (affineSubdivisionFactor 0 * δ)
    have hzero : affineSubdivisionFactor 0 * δ = 0 := by simp [affineSubdivisionFactor]
    rw [hzero]
    exact affineSingularChainsIn_zero_mesh A (affineSingularMesh_le 0 A δ hc)
  | succ n ih =>
    have h : affineSingularMesh (n + 1) A δ ≤
        Submodule.comap (affineSingularSubdivision (n + 1))
          (affineSingularMesh (n + 1) A (affineSubdivisionFactor (n + 1) * δ)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, hd, rfl⟩
      change affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v) ∈
        affineSingularMesh (n + 1) A (affineSubdivisionFactor (n + 1) * δ)
      rw [affineSingularSubdivision_succ]
      let B := convexHull ℝ (range v)
      let D := Metric.diam (range v)
      have hB : Convex ℝ B := convex_convexHull ℝ (range v)
      have hvB : ∀ i, v i ∈ B := fun i => subset_convexHull ℝ (range v) ⟨i, rfl⟩
      have hD : 0 ≤ D := Metric.diam_nonneg
      have hδc := affineSingularMesh_boundary n B D (affineSingularMesh_generator (n + 1) B D v hvB le_rfl)
      have hS := ih hB D hδc
      have hSm : affineSingularSubdivision n
          ((integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v)) ∈
            affineSingularMesh n B (affineSubdivisionFactor (n + 1) * D) :=
        affineSingularMesh_mono n (Subset.refl B)
          (mul_le_mul_of_nonneg_right (affineSubdivisionFactor_le_succ n) hD) hS
      have hcone := affineSingularMesh_cone n (affineSimplexBarycenter_mem (n + 1) v hB hvB)
        (mul_nonneg (affineSubdivisionFactor_nonneg (n + 1)) hD)
          (fun x hx => affineSimplexBarycenter_dist_convexHull (n + 1) v hx) hSm
      exact affineSingularMesh_mono (n + 1) (convexHull_min (range_subset_iff.mpr hv) hA)
        (mul_le_mul_of_nonneg_left hd (affineSubdivisionFactor_nonneg (n + 1))) hcone
    exact h hc

end DifferentialGeometry.Topology
