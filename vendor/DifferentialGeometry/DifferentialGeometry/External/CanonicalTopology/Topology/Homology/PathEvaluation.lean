module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathChains

@[expose] public section

/-! # Evaluation of the same original path simplex -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- The actual singular path simplex evaluates the original path at the
original barycentric interval parameter. -/
theorem integralPathSimplex_apply (p : Path x y) (t : Convexity.StdSimplex ℝ (Fin 2)) :
    integralSingularSimplexEquiv 1 X (integralPathSimplex p) t =
      p (Convexity.StdSimplex.homeomorphI t) := by
  exact congrArg (fun f : C(Convexity.StdSimplex ℝ (Fin 2), X) => f t)
    ((integralSingularSimplexEquiv 1 X).apply_symm_apply
      (p.toContinuousMap.comp ⟨Convexity.StdSimplex.homeomorphI,
        Convexity.StdSimplex.homeomorphI.continuous⟩))

end DifferentialGeometry.Topology
