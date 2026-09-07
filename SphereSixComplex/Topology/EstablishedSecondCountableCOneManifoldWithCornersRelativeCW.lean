module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Relative triangulation of manifolds with corners

This file records the relative-CW consequence of the classical compatible-triangulation theorem
for second-countable `C¹` manifolds with corners.  Only compatibility with the full boundary is
retained in the statement below.

The Cairns–Whitehead theorem for `C^k` manifolds with corners, including `k = 1`, is
explicitly stated in Murayama–Shiota, *Triangulation of the map of a G-manifold to its orbit
space*, Nagoya Math. J. 212 (2013), pp. 159–160, with Munkres, *Elementary Differential
Topology*, as the classical reference. A triangulation as a PL manifold carries its full
boundary as a subcomplex; forgetting that subcomplex’s cells gives the relative CW structure.

Source: https://doi.org/10.1215/00277630-2366201
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
