module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineNaturality

@[expose] public section

/-! # Naturality of the original affine subdivision under face maps -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

/-- Original continuous-map chain images commute with the original boundary. -/
theorem integralSingularChainMap_boundary {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (c : (integralSingularChains X).X (n + 1)) :
    (integralSingularChainMap f).f n ((integralSingularChains X).d (n + 1) n c) =
      (integralSingularChains Y).d (n + 1) n ((integralSingularChainMap f).f (n + 1) c) :=
  (congrArg (fun h : (integralSingularChains X).X (n + 1) ⟶
    (integralSingularChains Y).X n => h c) ((integralSingularChainMap f).comm (n + 1) n)).symm

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The original continuous-linear chain map commutes with the constructed
affine subdivision, even for maps collapsing the simplex dimension. -/
theorem affineSingularSubdivision_linear (n : ℕ) (f : E →L[ℝ] F)
    {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    (integralSingularChainMap ⟨f, f.continuous⟩).f n (affineSingularSubdivision n c) =
      affineSingularSubdivision n ((integralSingularChainMap ⟨f, f.continuous⟩).f n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let D := ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)).hom.comp
      (affineSingularSubdivision (n + 1)) - (affineSingularSubdivision (n + 1)).comp
        ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)).hom
    have h : affineSingularChainsIn (n + 1) A ≤ LinearMap.ker D := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change D (affineSingularChain (n + 1) v) = 0
      apply sub_eq_zero.mpr
      have hgen := affineSingularChain_mem (n + 1) A v hv
      have hδ := affineSingularChainsIn_boundary n A hgen
      have hS := affineSingularSubdivision_mem n hA hδ
      change (integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)
        (affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v)) =
          affineSingularSubdivision (n + 1) ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)
            (affineSingularChain (n + 1) v))
      rw [affineSingularSubdivision_succ, affineSingularCone_linear n f _ A hS, ih hδ,
        integralSingularChainMap_boundary, affineSingularChain_linear, affineSimplexBarycenter_linear,
        affineSingularSubdivision_succ]
    exact sub_eq_zero.mp (h hc)

end DifferentialGeometry.Topology
