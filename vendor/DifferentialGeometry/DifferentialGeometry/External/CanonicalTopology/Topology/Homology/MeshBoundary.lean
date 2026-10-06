module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineMesh

@[expose] public section

/-! # The original boundary preserves actual affine mesh -/

noncomputable section

open CategoryTheory Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Deleting original vertices cannot enlarge the actual diameter, so the
same original singular boundary preserves the specified affine mesh. -/
theorem affineSingularMesh_boundary (n : ℕ) (A : Set E) (δ : ℝ)
    {c : (integralSingularChains E).X (n + 1)} (hc : c ∈ affineSingularMesh (n + 1) A δ) :
    (integralSingularChains E).d (n + 1) n c ∈ affineSingularMesh n A δ := by
  have h : affineSingularMesh (n + 1) A δ ≤
      Submodule.comap ((integralSingularChains E).d (n + 1) n).hom (affineSingularMesh n A δ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, hd, rfl⟩
    change (integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v) ∈
      affineSingularMesh n A δ
    rw [affineSingularChain_boundary]
    apply Submodule.sum_mem
    intro i _
    apply (affineSingularMesh n A δ).toAddSubgroup.zsmul_mem
    apply affineSingularMesh_generator n A δ (v ∘ i.succAbove) (fun j => hv _)
    apply le_trans _ hd
    apply Metric.diam_mono _ (finite_range v).isBounded
    rintro _ ⟨j, rfl⟩
    exact ⟨i.succAbove j, rfl⟩
  exact h hc

end DifferentialGeometry.Topology
