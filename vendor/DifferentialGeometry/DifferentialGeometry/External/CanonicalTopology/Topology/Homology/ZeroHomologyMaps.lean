module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroChainClasses
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps

@[expose] public section

/-! # Actual H0 maps depend only on the original path components -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every original zero-simplex is the vertex at its SAME actual point. -/
theorem integralSimplexChain_zero_vertex (σ : integralSingularSimplex 0 X) :
    integralSimplexChain 0 σ = integralVertexChain (TopCat.toSSetObj₀Equiv σ) := by
  unfold integralVertexChain
  rw [Equiv.symm_apply_apply]

/-- The original chain map takes a vertex to the vertex at its SAME image point. -/
theorem integralVertexChain_map (f : C(X, Y)) (x : X) :
    (integralSingularChainMap f).f 0 (integralVertexChain x) = integralVertexChain (f x) := by
  unfold integralVertexChain
  rw [integralSimplexChain_map]
  rfl

/-- Joined original points have equal actual H0 classes, using their
SAME original path as the bounding one-chain. -/
theorem integralZeroVertexClass_eq_of_joined {x y : X} (h : Joined x y) :
    integralZeroChainClass (integralVertexChain x) = integralZeroChainClass (integralVertexChain y) := by
  obtain ⟨p⟩ := h
  exact ((integralZeroChainClass_eq_iff (integralVertexChain y) (integralVertexChain x)).mpr
    ⟨integralPathChain p, integralPathChain_boundary p⟩).symm

/-- Two actual continuous maps induce the SAME original H0 map whenever
their values at each original point lie in the same path component.
No jointly continuous homotopy is assumed. -/
theorem integralSingularHomologyMap_zero_eq_of_joined (f g : C(X, Y))
    (h : ∀ x, Joined (f x) (g x)) : integralSingularHomologyMap 0 f = integralSingularHomologyMap 0 g := by
  have he : (integralSingularHomologyMap 0 f).comp integralZeroChainClass =
      (integralSingularHomologyMap 0 g).comp integralZeroChainClass := by
    apply (integralSingularChainBasis 0 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
    rw [integralSimplexChain_zero_vertex, integralZeroChainClass_map, integralZeroChainClass_map,
      integralVertexChain_map, integralVertexChain_map]
    exact integralZeroVertexClass_eq_of_joined (h _)
  apply LinearMap.ext
  intro a
  obtain ⟨c, rfl⟩ := integralZeroChainClass_surjective a
  exact LinearMap.congr_fun he c

end DifferentialGeometry.Topology
