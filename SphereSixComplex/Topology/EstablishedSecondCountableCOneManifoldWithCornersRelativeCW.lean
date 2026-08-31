module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Relative triangulation of manifolds with corners

This file records the relative-CW consequence of the classical compatible-triangulation theorem
for second-countable `C¹` manifolds with corners.  Only compatibility with the full boundary is
retained in the statement below.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

universe u

/-- Every second-countable Hausdorff `C¹` manifold modelled on a finite-dimensional real
quadrant admits a CW decomposition relative to its full boundary. -/
public axiom establishedSecondCountableCOneManifoldWithCornersRelativeCW
    (n : ℕ) (X : Type u) [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [ChartedSpace (EuclideanQuadrant n) X]
    [IsManifold (modelWithCornersEuclideanQuadrant n) 1 X] :
    RelCWComplex (Set.univ : Set X)
      ((modelWithCornersEuclideanQuadrant n).boundary X)

end SphereSixComplex

end

end
