module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionMesh
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-! # Finite original chains and iterated geometric mesh shrinking -/

noncomputable section

open CategoryTheory Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every original affine chain has a finite positive mesh bound in its
same vertex carrier. The proof uses finite linear generation. -/
theorem affineSingularChainsIn_exists_mesh (n : ℕ) (A : Set E)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    ∃ δ : ℝ, 0 < δ ∧ c ∈ affineSingularMesh n A δ := by
  change c ∈ Submodule.span ℤ _ at hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v, hv, rfl⟩ := hc
    refine ⟨max 1 (Metric.diam (range v)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    exact affineSingularMesh_generator n A _ v hv (le_max_right _ _)
  | zero => exact ⟨1, zero_lt_one, Submodule.zero_mem _⟩
  | add c d _ _ hc hd =>
    obtain ⟨δ, hδ, hc⟩ := hc
    obtain ⟨ε, _, hd⟩ := hd
    refine ⟨max δ ε, hδ.trans_le (le_max_left _ _), ?_⟩
    exact Submodule.add_mem _ (affineSingularMesh_mono n (Subset.refl A) (le_max_left δ ε) hc)
      (affineSingularMesh_mono n (Subset.refl A) (le_max_right δ ε) hd)
  | smul a c _ hc =>
    obtain ⟨δ, hδ, hc⟩ := hc
    exact ⟨δ, hδ, Submodule.smul_mem _ a hc⟩

/-- Iteration of the SAME original affine subdivision endomorphism. -/
def affineSubdivisionIterate (n k : ℕ) :
    (integralSingularChains E).X n →ₗ[ℤ] (integralSingularChains E).X n :=
  (affineSingularSubdivision n) ^ k

/-- One more iteration applies the same subdivision to the preceding chain. -/
theorem affineSubdivisionIterate_succ (n k : ℕ) (c : (integralSingularChains E).X n) :
    affineSubdivisionIterate n (k + 1) c = affineSingularSubdivision n (affineSubdivisionIterate n k c) := by
  unfold affineSubdivisionIterate
  rw [pow_succ']
  rfl

/-- After k subdivisions the actual original mesh is at most (n/(n+1))^k δ. -/
theorem affineSubdivisionIterate_mesh (n k : ℕ) {A : Set E} (hA : Convex ℝ A) (δ : ℝ)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularMesh n A δ) :
    affineSubdivisionIterate n k c ∈ affineSingularMesh n A ((affineSubdivisionFactor n) ^ k * δ) := by
  induction k with
  | zero =>
    change c ∈ affineSingularMesh n A (affineSubdivisionFactor n ^ 0 * δ)
    simpa only [pow_zero, one_mul] using hc
  | succ k ih =>
    rw [affineSubdivisionIterate_succ]
    have h := affineSingularSubdivision_mesh n hA _ ih
    have he : affineSubdivisionFactor n * (affineSubdivisionFactor n ^ k * δ) =
        affineSubdivisionFactor n ^ (k + 1) * δ := by rw [pow_succ']; ring
    rwa [he] at h

/-- Any original affine chain becomes arbitrarily fine after finitely many
iterations, while staying in the same actual convex carrier. -/
theorem exists_affineSubdivisionIterate_fine (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, affineSubdivisionIterate n k c ∈ affineSingularMesh n A ε := by
  obtain ⟨δ, hδ, hcδ⟩ := affineSingularChainsIn_exists_mesh n A hc
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hδ) (affineSubdivisionFactor_lt_one n)
  exact ⟨k, affineSingularMesh_mono n (Subset.refl A) ((lt_div_iff₀ hδ).mp hk).le
    (affineSubdivisionIterate_mesh n k hA δ hcδ)⟩

end DifferentialGeometry.Topology
