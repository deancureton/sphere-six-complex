module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionNaturality

@[expose] public section

/-! # Naturality of the same affine subdivision homotopy -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The SAME constructed homotopy commutes with original continuous-linear
chain maps, including all ordered face maps and degenerate image simplices. -/
theorem affineSubdivisionHomotopy_linear (n : ℕ) (f : E →L[ℝ] F)
    {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    (integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1) (affineSubdivisionHomotopy n c) =
      affineSubdivisionHomotopy n ((integralSingularChainMap ⟨f, f.continuous⟩).f n c) := by
  induction n with
  | zero => simp only [affineSubdivisionHomotopy_zero, map_zero]
  | succ n ih =>
    let D := ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 2)).hom.comp
      (affineSubdivisionHomotopy (n + 1)) - (affineSubdivisionHomotopy (n + 1)).comp
        ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)).hom
    have h : affineSingularChainsIn (n + 1) A ≤ LinearMap.ker D := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change D (affineSingularChain (n + 1) v) = 0
      apply sub_eq_zero.mpr
      have hgen := affineSingularChain_mem (n + 1) A v hv
      have hδ := affineSingularChainsIn_boundary n A hgen
      have hb := Submodule.sub_mem (affineSingularChainsIn (n + 1) A)
        (Submodule.sub_mem _ hgen (affineSingularSubdivision_mem (n + 1) hA hgen))
          (affineSubdivisionHomotopy_mem n hA hδ)
      change (integralSingularChainMap ⟨f, f.continuous⟩).f (n + 2)
        (affineSubdivisionHomotopy (n + 1) (affineSingularChain (n + 1) v)) =
          affineSubdivisionHomotopy (n + 1) ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)
            (affineSingularChain (n + 1) v))
      rw [affineSubdivisionHomotopy_succ, affineSingularCone_linear (n + 1) f _ A hb]
      simp only [map_sub]
      rw [affineSingularSubdivision_linear (n + 1) f hA hgen, ih hδ,
        integralSingularChainMap_boundary, affineSingularChain_linear, affineSimplexBarycenter_linear,
        affineSubdivisionHomotopy_succ]
      simp only [map_sub]
    exact sub_eq_zero.mp (h hc)

end DifferentialGeometry.Topology
