module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionIterationHomotopy

@[expose] public section

/-! # Actual images of fine original affine chains are small -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] {ι : Type v}

/-- Exact restriction of any original coefficient-one simplex. -/
theorem integralSingularChainRestriction_simplex (n : ℕ) (A : Set X)
    (σ : integralSingularSimplex n X) (hσ : range (integralSingularSimplexEquiv n X σ) ⊆ A) :
    integralSingularChainRestriction n A
      ⟨integralSimplexChain n σ, Submodule.subset_span ⟨σ, hσ, rfl⟩⟩ =
        integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ) := by
  apply integralSingularChainInclusion_injective n A
  rw [integralSingularChainRestriction_inclusion, integralSimplexChain_map,
    integralSingularSimplexRestriction_inclusion]

/-- All points of the SAME affine simplex are within its original vertex
diameter of its zeroth vertex. -/
theorem affineSimplexMap_dist_vertex_zero (n : ℕ) (v : Fin (n + 1) → E)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplexMap v t) (v 0) ≤ Metric.diam (range v) := by
  have hb : Bornology.IsBounded (convexHull ℝ (range v)) :=
    isBounded_convexHull.mpr (Set.finite_range v).isBounded
  simpa only [convexHull_diam] using Metric.dist_le_diam_of_mem hb
    (affineSimplexMap_mem_convexHull v t) (subset_convexHull ℝ (range v) ⟨0, rfl⟩)

/-- If the actual image of every radius-δ ball in a convex carrier lies
in one member of U, every original affine chain of mesh ε < δ maps to an
original U-small chain after exact restriction to that SAME carrier. -/
theorem fineAffineChain_image_small (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    (f : C(A, X)) (U : ι → Set X) {δ ε : ℝ} (hεδ : ε < δ)
    (hδ : ∀ a : A, ∃ i, ∀ b : A, dist b a < δ → f b ∈ U i)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularMesh n A ε)
    (hcarrier : c ∈ integralSingularChainsIn n A) :
    (integralSingularChainMap f).f n
      (integralSingularChainRestriction n A ⟨c, hcarrier⟩) ∈ integralSingularSmallChains n U := by
  let F : integralSingularChainsIn n A →ₗ[ℤ] (integralSingularChains X).X n :=
    ((integralSingularChainMap f).f n).hom.comp (integralSingularChainRestriction n A)
  change F ⟨c, hcarrier⟩ ∈ integralSingularSmallChains n U
  let Q := (Submodule.comap F (integralSingularSmallChains n U)).map
    (integralSingularChainsIn n A).subtype
  have h : affineSingularMesh n A ε ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, hdiam, rfl⟩
    obtain ⟨i, hi⟩ := hδ ⟨v 0, hv 0⟩
    have hσ : range (integralSingularSimplexEquiv n E (affineSingularSimplex n v)) ⊆ A := by
      rintro _ ⟨t, rfl⟩
      change affineSimplexMap v t ∈ A
      exact (convexHull_min (by rintro _ ⟨j, rfl⟩; exact hv j) hA)
        (affineSimplexMap_mem_convexHull v t)
    have hvcarrier := affineSingularChainsIn_le n hA (affineSingularChain_mem n A v hv)
    refine ⟨⟨affineSingularChain n v, hvcarrier⟩, ?_, rfl⟩
    change (integralSingularChainMap f).f n
      (integralSingularChainRestriction n A ⟨integralSimplexChain n (affineSingularSimplex n v), hvcarrier⟩) ∈ integralSingularSmallChains n U
    rw [integralSingularChainRestriction_simplex n A _ hσ, integralSimplexChain_map]
    apply Submodule.mem_iSup_of_mem i
    apply Submodule.subset_span
    refine ⟨_, ?_, rfl⟩
    rintro _ ⟨t, rfl⟩
    rw [integralSingularSimplexMap_apply]
    apply hi
    change dist (affineSimplexMap v t) (v 0) < δ
    exact ((affineSimplexMap_dist_vertex_zero n v t).trans hdiam).trans_lt hεδ
  obtain ⟨b, hb, he⟩ := h hc
  have he' : b = ⟨c, hcarrier⟩ := Subtype.ext he
  rw [← he']
  exact hb

end DifferentialGeometry.Topology
