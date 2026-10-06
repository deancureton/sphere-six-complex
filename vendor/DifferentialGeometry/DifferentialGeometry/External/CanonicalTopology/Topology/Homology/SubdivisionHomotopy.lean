module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionBoundary

@[expose] public section

/-! # The original affine subdivision homotopy and its carriers -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Recursively cone the difference between the same original chain and
its subdivision, corrected by the homotopy of its original boundary. -/
def affineSubdivisionHomotopy (n : ℕ) :
    (integralSingularChains E).X n →ₗ[ℤ] (integralSingularChains E).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => by
    classical
    exact (integralSingularChainBasis (n + 1) E).constr
      (M' := (integralSingularChains E).X (n + 2)) ℕ (fun σ =>
        if h : ∃ v, affineSingularSimplex (n + 1) v = σ then
          affineSingularCone (n + 1) (affineSimplexBarycenter (n + 1) h.choose)
            (integralSimplexChain (n + 1) σ -
              affineSingularSubdivision (n + 1) (integralSimplexChain (n + 1) σ) -
              affineSubdivisionHomotopy n ((integralSingularChains E).d (n + 1) n
                (integralSimplexChain (n + 1) σ))) else 0)

/-- The original degree-zero homotopy is zero, since subdivision is identity. -/
theorem affineSubdivisionHomotopy_zero (c : (integralSingularChains E).X 0) :
    affineSubdivisionHomotopy 0 c = 0 := rfl

/-- The homotopy recursion uses the same original affine generator and
its exact subdivision and boundary. -/
theorem affineSubdivisionHomotopy_succ (n : ℕ) (v : Fin (n + 2) → E) :
    affineSubdivisionHomotopy (n + 1) (affineSingularChain (n + 1) v) =
      affineSingularCone (n + 1) (affineSimplexBarycenter (n + 1) v)
        (affineSingularChain (n + 1) v -
          affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v) -
          affineSubdivisionHomotopy n ((integralSingularChains E).d (n + 1) n
            (affineSingularChain (n + 1) v))) := by
  classical
  rw [affineSubdivisionHomotopy]
  change ((integralSingularChainBasis (n + 1) E).constr
    (M' := (integralSingularChains E).X (n + 2)) ℕ _)
      (integralSimplexChain (n + 1) (affineSingularSimplex (n + 1) v)) = _
  rw [← integralSingularChainBasis_apply, Basis.constr_basis]
  let h : ∃ w, affineSingularSimplex (n + 1) w = affineSingularSimplex (n + 1) v := ⟨v, rfl⟩
  rw [dite_eq_left h, affineSingularSimplex_injective (n + 1) h.choose_spec]
  rfl

/-- The same actual convex carrier is preserved by every homotopy component. -/
theorem affineSubdivisionHomotopy_mem (n : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    affineSubdivisionHomotopy n c ∈ affineSingularChainsIn (n + 1) A := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    have h : affineSingularChainsIn (n + 1) A ≤
        Submodule.comap (affineSubdivisionHomotopy (n + 1)) (affineSingularChainsIn (n + 2) A) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change affineSubdivisionHomotopy (n + 1) (affineSingularChain (n + 1) v) ∈
        affineSingularChainsIn (n + 2) A
      rw [affineSubdivisionHomotopy_succ]
      have hgen := affineSingularChain_mem (n + 1) A v hv
      exact affineSingularCone_mem (n + 1) (affineSimplexBarycenter_mem (n + 1) v hA hv)
        (Submodule.sub_mem _ (Submodule.sub_mem _ hgen
          (affineSingularSubdivision_mem (n + 1) hA hgen))
            (ih (affineSingularChainsIn_boundary n A hgen)))
    exact h hc

end DifferentialGeometry.Topology
