module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary

@[expose] public section

/-! # The original image simplices and coefficient-one chain maps -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original image singular simplex under the actual continuous map. -/
def integralSingularSimplexMap (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplex n Y :=
  (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op ⦋n⦌) σ

/-- Its continuous map is exactly postcomposition of the original simplex. -/
theorem integralSingularSimplexMap_apply (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplexEquiv n Y (integralSingularSimplexMap n f σ) =
      f.comp (integralSingularSimplexEquiv n X σ) := rfl

/-- The original chain map takes a coefficient-one simplex to its same
coefficient-one image simplex. -/
theorem integralSimplexChain_map (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    (integralSingularChainMap f).f n (integralSimplexChain n σ) =
      integralSimplexChain n (integralSingularSimplexMap n f σ) := by
  exact congrArg (fun h : integralSingularCoefficients.{u} ⟶
    (integralSingularChains Y).X n => h (ULift.up 1))
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
        (TopCat.toSSet.map (TopCat.ofHom f))
        integralSingularCoefficients σ)

end DifferentialGeometry.Topology
