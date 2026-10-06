module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionHomotopy

@[expose] public section

/-! # The exact affine subdivision homotopy identity -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constructed homotopy has the exact original identity-minus-subdivision
boundary equation, on every affine chain in the same convex carrier. -/
theorem affineSubdivisionHomotopy_boundary (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X (n + 1)} (hc : c ∈ affineSingularChainsIn (n + 1) A) :
    (integralSingularChains E).d (n + 2) (n + 1) (affineSubdivisionHomotopy (n + 1) c) =
      c - affineSingularSubdivision (n + 1) c -
        affineSubdivisionHomotopy n ((integralSingularChains E).d (n + 1) n c) := by
  induction n with
  | zero =>
    let F := ((integralSingularChains E).d 2 1).hom.comp (affineSubdivisionHomotopy 1) -
      (LinearMap.id - affineSingularSubdivision 1 -
        (affineSubdivisionHomotopy 0).comp ((integralSingularChains E).d 1 0).hom)
    have h : affineSingularChainsIn 1 A ≤ LinearMap.ker F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change F (affineSingularChain 1 v) = 0
      apply sub_eq_zero.mpr
      have hgen := affineSingularChain_mem 1 A v hv
      have hb : affineSingularChain 1 v - affineSingularSubdivision 1 (affineSingularChain 1 v) ∈
          affineSingularChainsIn 1 A :=
        Submodule.sub_mem _ hgen (affineSingularSubdivision_mem 1 hA hgen)
      have hz : (integralSingularChains E).d 1 0
          (affineSingularChain 1 v - affineSingularSubdivision 1 (affineSingularChain 1 v)) = 0 := by
        rw [map_sub, affineSingularSubdivision_boundary 0 hA hgen, affineSingularSubdivision_zero,
          sub_self]
      change (integralSingularChains E).d 2 1
        (affineSubdivisionHomotopy 1 (affineSingularChain 1 v)) = _
      rw [affineSubdivisionHomotopy_succ, affineSubdivisionHomotopy_zero, sub_zero,
        affineSingularCone_boundary 0 _ A hb, hz, map_zero, sub_zero]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        affineSubdivisionHomotopy_zero, sub_zero]
    exact sub_eq_zero.mp (h hc)
  | succ n ih =>
    let F := ((integralSingularChains E).d (n + 3) (n + 2)).hom.comp
      (affineSubdivisionHomotopy (n + 2)) -
        (LinearMap.id - affineSingularSubdivision (n + 2) -
          (affineSubdivisionHomotopy (n + 1)).comp ((integralSingularChains E).d (n + 2) (n + 1)).hom)
    have h : affineSingularChainsIn (n + 2) A ≤ LinearMap.ker F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change F (affineSingularChain (n + 2) v) = 0
      apply sub_eq_zero.mpr
      have hgen := affineSingularChain_mem (n + 2) A v hv
      have hδ := affineSingularChainsIn_boundary (n + 1) A hgen
      have hb := Submodule.sub_mem (affineSingularChainsIn (n + 2) A)
        (Submodule.sub_mem _ hgen (affineSingularSubdivision_mem (n + 2) hA hgen))
          (affineSubdivisionHomotopy_mem (n + 1) hA hδ)
      have hz : (integralSingularChains E).d (n + 2) (n + 1)
          (affineSingularChain (n + 2) v - affineSingularSubdivision (n + 2) (affineSingularChain (n + 2) v) -
            affineSubdivisionHomotopy (n + 1)
              ((integralSingularChains E).d (n + 2) (n + 1) (affineSingularChain (n + 2) v))) = 0 := by
        rw [map_sub, map_sub, affineSingularSubdivision_boundary (n + 1) hA hgen, ih hδ]
        have hdd : (integralSingularChains E).d (n + 1) n
            ((integralSingularChains E).d (n + 2) (n + 1) (affineSingularChain (n + 2) v)) = 0 :=
          congrArg (fun f : (integralSingularChains E).X (n + 2) ⟶
            (integralSingularChains E).X n => f (affineSingularChain (n + 2) v))
              ((integralSingularChains E).d_comp_d (n + 2) (n + 1) n)
        rw [hdd, map_zero]
        abel
      change (integralSingularChains E).d (n + 3) (n + 2)
        (affineSubdivisionHomotopy (n + 2) (affineSingularChain (n + 2) v)) = _
      rw [affineSubdivisionHomotopy_succ, affineSingularCone_boundary (n + 1) _ A hb,
        hz, map_zero, sub_zero]
      rfl
    exact sub_eq_zero.mp (h hc)

end DifferentialGeometry.Topology
