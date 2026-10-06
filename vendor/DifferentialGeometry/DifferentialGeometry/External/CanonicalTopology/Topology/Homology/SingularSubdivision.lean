module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexEvaluation
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionHomotopyNaturality

@[expose] public section

/-! # Subdivision and its same homotopy on all original singular chains -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

/-- The original universal affine subdivision, exactly restricted to its
same lifted simplex body. -/
def universalSimplexSubdivision (n : ℕ) : integralSingularChainsIn n (liftedSimplexBody.{u} n) :=
  ⟨affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex n)),
    affineSingularChainsIn_le n (convex_liftedSimplexBody n)
      (affineSingularSubdivision_mem n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n))⟩

/-- The SAME universal affine homotopy, carried by the same lifted simplex body. -/
def universalSimplexHomotopy (n : ℕ) : integralSingularChainsIn (n + 1) (liftedSimplexBody.{u} n) :=
  ⟨affineSubdivisionHomotopy n (affineSingularChain n (liftedSimplexVertex n)),
    affineSingularChainsIn_le (n + 1) (convex_liftedSimplexBody n)
      (affineSubdivisionHomotopy_mem n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n))⟩

variable {X : Type u} [TopologicalSpace X]

/-- Subdivision on EVERY original singular simplex, by evaluation of its
same universal subdivided simplex, extended on the original singular basis. -/
def integralSingularSubdivision (n : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X n :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains X).X n) ℕ
    (fun σ => singularSimplexChainPush n n σ (universalSimplexSubdivision n))

/-- Exact evaluation formula on each original coefficient-one singular simplex. -/
theorem integralSingularSubdivision_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivision n (integralSimplexChain n σ) =
      singularSimplexChainPush n n σ (universalSimplexSubdivision n) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

/-- The original universal homotopy similarly acts on EVERY original singular simplex. -/
def integralSingularSubdivisionHomotopy (n : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X (n + 1) :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains X).X (n + 1)) ℕ
    (fun σ => singularSimplexChainPush n (n + 1) σ (universalSimplexHomotopy n))

/-- The same homotopy component on each original coefficient-one simplex. -/
theorem integralSingularSubdivisionHomotopy_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivisionHomotopy n (integralSimplexChain n σ) =
      singularSimplexChainPush n (n + 1) σ (universalSimplexHomotopy n) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

/-- Subdivision is the original identity in degree zero. -/
theorem integralSingularSubdivision_zero :
    integralSingularSubdivision (X := X) 0 = LinearMap.id := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, integralSingularSubdivision_simplex]
  exact singularSimplexChainPush_identity 0 σ

/-- The SAME homotopy has zero degree-zero component. -/
theorem integralSingularSubdivisionHomotopy_zero :
    integralSingularSubdivisionHomotopy (X := X) 0 = 0 := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, integralSingularSubdivisionHomotopy_simplex]
  exact (singularSimplexChainPush 0 1 σ).map_zero

end DifferentialGeometry.Topology
