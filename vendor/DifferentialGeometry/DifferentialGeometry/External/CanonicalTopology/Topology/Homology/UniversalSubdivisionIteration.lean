module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SingularSubdivisionIteration

@[expose] public section

/-! # Evaluating iterates of the same universal simplex chain -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Exact restriction commutes with every original subdivision iterate. -/
theorem integralSingularSubdivisionIterate_restriction (n k : ℕ) (A : Set X)
    (c : integralSingularChainsIn n A) :
    integralSingularChainRestriction n A
      ⟨integralSingularSubdivisionIterate n k c.val, integralSingularSubdivisionIterate_mem n k A c.property⟩ =
        integralSingularSubdivisionIterate n k (integralSingularChainRestriction n A c) := by
  apply integralSingularChainInclusion_injective n A
  rw [integralSingularChainRestriction_inclusion, ← integralSingularSubdivisionIterate_map,
    integralSingularChainRestriction_inclusion]

/-- Evaluation through the SAME original simplex commutes with each iterate. -/
theorem singularSimplexChainPush_iterate (n m k : ℕ) (σ : integralSingularSimplex n X)
    (c : integralSingularChainsIn m (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush n m σ
      ⟨integralSingularSubdivisionIterate m k c.val,
        integralSingularSubdivisionIterate_mem m k _ c.property⟩ =
          integralSingularSubdivisionIterate m k (singularSimplexChainPush n m σ c) := by
  unfold singularSimplexChainPush
  rw [LinearMap.comp_apply, integralSingularSubdivisionIterate_restriction,
    ← integralSingularSubdivisionIterate_map]
  rfl

/-- Every subdivision of an original coefficient-one simplex is the
image of the SAME geometrically shrinking universal affine iterate. -/
theorem integralSingularSubdivisionIterate_simplex (n k : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivisionIterate n k (integralSimplexChain n σ) =
      singularSimplexChainPush n n σ
        ⟨affineSubdivisionIterate n k (affineSingularChain n (liftedSimplexVertex n)),
          affineSingularChainsIn_le n (convex_liftedSimplexBody n)
            (affineSingularMesh_le n _ _ (affineSubdivisionIterate_mesh n k (convex_liftedSimplexBody n)
              (Metric.diam (range (liftedSimplexVertex n)))
              (affineSingularMesh_generator n _ _ _ (liftedSimplexVertex_mem n) le_rfl)))⟩ := by
  have h := singularSimplexChainPush_iterate n n k σ
    ⟨affineSingularChain n (liftedSimplexVertex n),
      affineSingularChainsIn_le n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n)⟩
  rw [singularSimplexChainPush_identity] at h
  rw [← h]
  congr 1
  apply Subtype.ext
  exact integralSingularSubdivisionIterate_affine n k (convex_liftedSimplexBody n) (liftedSimplexChain_mem n)

end DifferentialGeometry.Topology
