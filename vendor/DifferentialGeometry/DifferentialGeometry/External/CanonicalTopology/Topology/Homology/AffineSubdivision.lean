module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineZeroCone

@[expose] public section

/-! # Barycentric subdivision of the original affine singular chains -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual barycenter of the specified original ordered vertices. -/
def affineSimplexBarycenter (n : ℕ) (v : Fin (n + 1) → E) : E :=
  affineSimplexMap v Convexity.StdSimplex.barycenter

/-- This barycenter lies in every convex carrier of the original vertices. -/
theorem affineSimplexBarycenter_mem (n : ℕ) (v : Fin (n + 1) → E)
    {A : Set E} (hA : Convex ℝ A) (hv : ∀ i, v i ∈ A) : affineSimplexBarycenter n v ∈ A :=
  convexHull_min (range_subset_iff.mpr hv) hA (affineSimplexMap_mem_convexHull v _)

/-- Recursive barycentric subdivision: cone the subdivided original
boundary to the same simplex's actual barycenter. It acts on the original
chain groups and sends nonaffine basis simplices to zero in positive degrees. -/
def affineSingularSubdivision (n : ℕ) :
    (integralSingularChains E).X n →ₗ[ℤ] (integralSingularChains E).X n :=
  match n with
  | 0 => LinearMap.id
  | n + 1 => by
    classical
    exact (integralSingularChainBasis (n + 1) E).constr
      (M' := (integralSingularChains E).X (n + 1)) ℕ (fun σ =>
        if h : ∃ v, affineSingularSimplex (n + 1) v = σ then
          affineSingularCone n (affineSimplexBarycenter (n + 1) h.choose)
            (affineSingularSubdivision n ((integralSingularChains E).d (n + 1) n
              (integralSimplexChain (n + 1) σ))) else 0)

/-- Degree-zero subdivision is the original identity. -/
theorem affineSingularSubdivision_zero (c : (integralSingularChains E).X 0) :
    affineSingularSubdivision 0 c = c := rfl

/-- The recursion on an affine generator uses its exact original vertices
and boundary, independently of the proof that it is affine. -/
theorem affineSingularSubdivision_succ (n : ℕ) (v : Fin (n + 2) → E) :
    affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v) =
      affineSingularCone n (affineSimplexBarycenter (n + 1) v)
        (affineSingularSubdivision n ((integralSingularChains E).d (n + 1) n
          (affineSingularChain (n + 1) v))) := by
  classical
  rw [affineSingularSubdivision]
  change ((integralSingularChainBasis (n + 1) E).constr
    (M' := (integralSingularChains E).X (n + 1)) ℕ _)
      (integralSimplexChain (n + 1) (affineSingularSimplex (n + 1) v)) = _
  rw [← integralSingularChainBasis_apply, Basis.constr_basis]
  let h : ∃ w, affineSingularSimplex (n + 1) w = affineSingularSimplex (n + 1) v := ⟨v, rfl⟩
  rw [dite_eq_left h, affineSingularSimplex_injective (n + 1) h.choose_spec]
  rfl

/-- Subdivision preserves the same actual convex carrier in every degree. -/
theorem affineSingularSubdivision_mem (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    affineSingularSubdivision n c ∈ affineSingularChainsIn n A := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    have h : affineSingularChainsIn (n + 1) A ≤
        Submodule.comap (affineSingularSubdivision (n + 1)) (affineSingularChainsIn (n + 1) A) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v) ∈
        affineSingularChainsIn (n + 1) A
      rw [affineSingularSubdivision_succ]
      exact affineSingularCone_mem n (affineSimplexBarycenter_mem (n + 1) v hA hv)
        (ih (affineSingularChainsIn_boundary n A (affineSingularChain_mem (n + 1) A v hv)))
    exact h hc

end DifferentialGeometry.Topology
