module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineSubdivision

@[expose] public section

/-! # Subdivision commutes with the original affine-chain boundary -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Barycentric subdivision commutes with the original singular boundary
on every affine chain in the same convex carrier, including degree one. -/
theorem affineSingularSubdivision_boundary (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X (n + 1)} (hc : c ∈ affineSingularChainsIn (n + 1) A) :
    (integralSingularChains E).d (n + 1) n (affineSingularSubdivision (n + 1) c) =
      affineSingularSubdivision n ((integralSingularChains E).d (n + 1) n c) := by
  induction n with
  | zero =>
    let F := ((integralSingularChains E).d 1 0).hom.comp (affineSingularSubdivision 1) -
      (affineSingularSubdivision 0).comp ((integralSingularChains E).d 1 0).hom
    have h : affineSingularChainsIn 1 A ≤ LinearMap.ker F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change F (affineSingularChain 1 v) = 0
      apply sub_eq_zero.mpr
      change (integralSingularChains E).d 1 0
        (affineSingularSubdivision 1 (affineSingularChain 1 v)) = _
      rw [affineSingularSubdivision_succ, affineSingularSubdivision_zero]
      exact affineSingularCone_bounds_zero (affineSimplexBarycenter 1 v) A
        (affineSingularChainsIn_boundary 0 A (affineSingularChain_mem 1 A v hv))
          (LinearMap.congr_fun integralSingularAugmentation_boundary (affineSingularChain 1 v))
    exact sub_eq_zero.mp (h hc)
  | succ n ih =>
    let F := ((integralSingularChains E).d (n + 2) (n + 1)).hom.comp
      (affineSingularSubdivision (n + 2)) - (affineSingularSubdivision (n + 1)).comp
        ((integralSingularChains E).d (n + 2) (n + 1)).hom
    have h : affineSingularChainsIn (n + 2) A ≤ LinearMap.ker F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change F (affineSingularChain (n + 2) v) = 0
      apply sub_eq_zero.mpr
      have hδ := affineSingularChainsIn_boundary (n + 1) A
        (affineSingularChain_mem (n + 2) A v hv)
      have hS := affineSingularSubdivision_mem (n + 1) hA hδ
      have hz := ih hδ
      have hdd : (integralSingularChains E).d (n + 1) n
          ((integralSingularChains E).d (n + 2) (n + 1) (affineSingularChain (n + 2) v)) = 0 :=
        congrArg (fun f : (integralSingularChains E).X (n + 2) ⟶
          (integralSingularChains E).X n => f (affineSingularChain (n + 2) v))
            ((integralSingularChains E).d_comp_d (n + 2) (n + 1) n)
      rw [hdd, map_zero] at hz
      change (integralSingularChains E).d (n + 2) (n + 1)
        (affineSingularSubdivision (n + 2) (affineSingularChain (n + 2) v)) = _
      rw [affineSingularSubdivision_succ, affineSingularCone_boundary n _ A hS,
        hz, map_zero, sub_zero]
      rfl
    exact sub_eq_zero.mp (h hc)

end DifferentialGeometry.Topology
