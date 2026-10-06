module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineChains

@[expose] public section

/-! # Linear cones on actual affine singular chains -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cone an original simplex when it is affine. The ordered vertex list
is determined by that actual simplex; other basis elements are sent to zero. -/
def affineSingularConeBasis (n : ℕ) (a : E) (σ : integralSingularSimplex n E) :
    (integralSingularChains E).X (n + 1) := by
  classical
  exact if h : ∃ v, affineSingularSimplex n v = σ then
    affineSingularChain (n + 1) (Fin.cons a h.choose) else 0

/-- On an affine simplex the cone uses its SAME original ordered vertices. -/
theorem affineSingularConeBasis_affine (n : ℕ) (a : E) (v : Fin (n + 1) → E) :
    affineSingularConeBasis n a (affineSingularSimplex n v) =
      affineSingularChain (n + 1) (Fin.cons a v) := by
  classical
  unfold affineSingularConeBasis
  let h : ∃ w, affineSingularSimplex n w = affineSingularSimplex n v := ⟨v, rfl⟩
  rw [dite_eq_left h, affineSingularSimplex_injective n h.choose_spec]

/-- Extend the actual affine cones linearly on the original singular basis. -/
def affineSingularCone (n : ℕ) (a : E) :
    (integralSingularChains E).X n →ₗ[ℤ] (integralSingularChains E).X (n + 1) :=
  (integralSingularChainBasis n E).constr (M' := (integralSingularChains E).X (n + 1)) ℕ
    (affineSingularConeBasis n a)

/-- The linear extension agrees exactly on every original affine generator. -/
theorem affineSingularCone_affine (n : ℕ) (a : E) (v : Fin (n + 1) → E) :
    affineSingularCone n a (affineSingularChain n v) =
      affineSingularChain (n + 1) (Fin.cons a v) := by
  change affineSingularCone n a (integralSimplexChain n (affineSingularSimplex n v)) = _
  rw [← integralSingularChainBasis_apply]
  exact ((integralSingularChainBasis n E).constr_basis ℕ _ (affineSingularSimplex n v)).trans
    (affineSingularConeBasis_affine n a v)

/-- The cone identity on each original positive-dimensional affine generator. -/
theorem affineSingularCone_boundary_affine (n : ℕ) (a : E) (v : Fin (n + 2) → E) :
    (integralSingularChains E).d (n + 2) (n + 1)
      (affineSingularCone (n + 1) a (affineSingularChain (n + 1) v)) =
        affineSingularChain (n + 1) v - affineSingularCone n a
          ((integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v)) := by
  rw [affineSingularCone_affine, affineSingularChain_cone_boundary,
    affineSingularChain_boundary, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, affineSingularCone_affine]

end DifferentialGeometry.Topology
