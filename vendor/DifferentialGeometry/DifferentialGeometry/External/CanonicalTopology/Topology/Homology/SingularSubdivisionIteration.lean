module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionAffineAgreement

@[expose] public section

/-! # Iteration on the same original singular chains -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {ι : Type v}

/-- Powers of the actual full subdivision operator. -/
def integralSingularSubdivisionIterate (n k : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X n :=
  (integralSingularSubdivision n) ^ k

/-- One further subdivision of the SAME original chain. -/
theorem integralSingularSubdivisionIterate_succ (n k : ℕ) (c : (integralSingularChains X).X n) :
    integralSingularSubdivisionIterate n (k + 1) c =
      integralSingularSubdivision n (integralSingularSubdivisionIterate n k c) := by
  unfold integralSingularSubdivisionIterate
  rw [pow_succ']
  rfl

/-- Every iterate commutes with the original continuous-map chain image. -/
theorem integralSingularSubdivisionIterate_map (n k : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X n) :
    integralSingularSubdivisionIterate n k ((integralSingularChainMap f).f n c) =
      (integralSingularChainMap f).f n (integralSingularSubdivisionIterate n k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [integralSingularSubdivisionIterate_succ, ih, integralSingularSubdivision_map,
      integralSingularSubdivisionIterate_succ]

/-- Every iterate commutes with the actual original boundary. -/
theorem integralSingularSubdivisionIterate_boundary (n k : ℕ)
    (c : (integralSingularChains X).X (n + 1)) :
    (integralSingularChains X).d (n + 1) n (integralSingularSubdivisionIterate (n + 1) k c) =
      integralSingularSubdivisionIterate n k ((integralSingularChains X).d (n + 1) n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [integralSingularSubdivisionIterate_succ]
    have h := LinearMap.congr_fun (integralSingularSubdivision_boundary n)
      (integralSingularSubdivisionIterate (n + 1) k c)
    change (integralSingularChains X).d (n + 1) n
      (integralSingularSubdivision (n + 1) (integralSingularSubdivisionIterate (n + 1) k c)) =
        integralSingularSubdivision n ((integralSingularChains X).d (n + 1) n
          (integralSingularSubdivisionIterate (n + 1) k c)) at h
    rw [h, ih, integralSingularSubdivisionIterate_succ]

/-- Iteration retains every original subspace carrier. -/
theorem integralSingularSubdivisionIterate_mem (n k : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    integralSingularSubdivisionIterate n k c ∈ integralSingularChainsIn n A := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [integralSingularSubdivisionIterate_succ]
    exact integralSingularSubdivision_mem n A ih

/-- Iteration retains original smallness for the SAME family. -/
theorem integralSingularSubdivisionIterate_small (n k : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivisionIterate n k c ∈ integralSingularSmallChains n U := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [integralSingularSubdivisionIterate_succ]
    exact integralSingularSubdivision_small n U ih

/-- On original affine chains in a convex carrier, the full iterate is
exactly the SAME geometrically shrinking affine iterate. -/
theorem integralSingularSubdivisionIterate_affine {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n k : ℕ) {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    integralSingularSubdivisionIterate n k c = affineSubdivisionIterate n k c := by
  obtain ⟨δ, _, hcδ⟩ := affineSingularChainsIn_exists_mesh n A hc
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [integralSingularSubdivisionIterate_succ, ih, affineSubdivisionIterate_succ]
    exact integralSingularSubdivision_affine n A
      (affineSingularMesh_le n A _ (affineSubdivisionIterate_mesh n k hA δ hcδ))

end DifferentialGeometry.Topology
